use std::fmt::Display;

use itertools::Itertools;

use crate::arch::Arch;
use crate::encoding::bitpattern::{
    FlowOutputLocation, FlowValueLocation, MappingOrBitOrder, Part, PartMapping, PartValue, PART_NAMES,
};
use crate::encoding::dataflows::{AccessKind, Dest, Inputs, Source};
use crate::encoding::Encoding;
use crate::semantics::{Computation, ARG_NAMES};

struct SourceWithParts<'a, A: Arch, C> {
    loc: FlowValueLocation,
    encoding: &'a Encoding<A, C>,
    input: &'a Source<A>,
}

impl<A: Arch, C> Display for SourceWithParts<'_, A, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.input {
            Source::Dest(Dest::Reg(reg, size)) => {
                let mut found = false;
                for (part_index, part) in self.encoding.parts.iter().enumerate() {
                    match &part.mapping {
                        PartMapping::Register {
                            locations,
                            mapping: _,
                        } if locations.contains(&self.loc) => {
                            write!(f, "<{}>", PART_NAMES[part_index])?;
                            found = true;
                        },
                        _ => {},
                    }
                }

                if !found {
                    write!(f, "{reg}")?;
                }

                write!(f, "[{}..{}]", size.start_byte, size.end_byte)?;
            },
            Source::Dest(Dest::Mem(mem, size)) => {
                write!(f, "m{mem}")?;

                write!(f, "[{}..{}]", size.start_byte, size.end_byte)?;
            },
            Source::Imm(imm) => {
                write!(f, "<{}>", PART_NAMES[*imm])?;
            },
            other => write!(f, "{other}")?,
        }

        Ok(())
    }
}

struct InputsWithParts<'a, A: Arch, X, C> {
    loc: FlowOutputLocation,
    encoding: &'a Encoding<A, X>,
    inputs: &'a Inputs<A>,
    computation: Option<&'a C>,
}

impl<A: Arch, X, C: Computation> Display for InputsWithParts<'_, A, X, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.computation {
            Some(computation) => {
                let names = self
                    .inputs
                    .iter()
                    .enumerate()
                    .map(|(index, input)| {
                        format!(
                            "{}",
                            SourceWithParts {
                                loc: self.loc.input(index).into(),
                                encoding: self.encoding,
                                input
                            }
                        )
                    })
                    .collect::<Vec<_>>();

                write!(f, "{}", computation.display(&names))?;
            },
            None => {
                for (index, input) in self.inputs.iter().enumerate() {
                    if index != 0 {
                        write!(f, ", ")?;
                    }

                    write!(
                        f,
                        "{}",
                        SourceWithParts {
                            loc: self.loc.input(index).into(),
                            encoding: self.encoding,
                            input
                        }
                    )?;
                }
            },
        }

        Ok(())
    }
}

impl<A: Arch, C: Computation> Display for Encoding<A, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{} [{}]",
            self.bits
                .iter()
                .rev()
                .chunks(8)
                .into_iter()
                .map(|byte| byte.into_iter().map(|s| format!("{s:?}")).join(""))
                .join(" "),
            self.dataflows
                .addresses
                .instr
                .bytes()
                .iter()
                .map(|b| format!("{b:02X}"))
                .join("")
        )?;
        writeln!(
            f,
            "Errors: {}",
            self.errors.iter().map(|&e| if e { "!" } else { "." }).join("")
        )?;

        for (index, access) in self.dataflows.addresses.iter().enumerate() {
            writeln!(
                f,
                "{:10} := {} (size {:?}, align {})",
                format!(
                    "Addr{}(m{})",
                    match access.kind {
                        AccessKind::Executable => "X ",
                        AccessKind::Input => "R ",
                        AccessKind::InputOutput => "RW",
                    },
                    index
                ),
                InputsWithParts {
                    encoding: self,
                    inputs: &access.inputs,
                    loc: FlowOutputLocation::MemoryAccess(index),
                    computation: Some(&access.calculation),
                },
                access.size,
                access.alignment,
            )?;
        }

        for (index, output) in self.dataflows.output_dataflows().enumerate() {
            writeln!(
                f,
                "{:10} := {}",
                format!(
                    "{}",
                    SourceWithParts {
                        encoding: self,
                        input: &Source::Dest(output.target),
                        loc: FlowValueLocation::Output(index)
                    }
                ),
                InputsWithParts {
                    encoding: self,
                    inputs: &output.inputs,
                    loc: FlowOutputLocation::Output(index),
                    computation: output.computation.as_ref(),
                }
            )?;
        }

        writeln!(f, "---")?;

        for (index, part) in self.parts.iter().enumerate() {
            writeln!(f, "<{}>{}", PART_NAMES[index], part)?;
        }

        if !self.write_ordering.is_empty() {
            writeln!(f, "write ordering: {:?}", self.write_ordering)?;
        }

        Ok(())
    }
}

struct DisplayPartMapping<'a, A: Arch> {
    mapping: &'a PartMapping<A>,
    value: u64,
    size: usize,
}

impl<A: Arch> Display for DisplayPartMapping<'_, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.mapping {
            PartMapping::Register {
                mapping, ..
            } => {
                for (key, value) in mapping.iter().enumerate() {
                    if key != 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{:0pad$b} => ", key, pad = self.size)?;
                    if let Some(reg) = value {
                        if key as u64 == self.value {
                            write!(f, "[ {reg} ]")?;
                        } else {
                            write!(f, "{reg}")?;
                        }
                    } else {
                        write!(f, "-")?;
                    }
                }
            },
            PartMapping::Imm {
                mapping,
                bits,
                ..
            } => {
                write!(f, "immediate = 0x{:X}", self.value)?;

                if let Some(MappingOrBitOrder::Mapping(mapping)) = mapping {
                    if mapping.iter().any(PartValue::is_invalid) {
                        for (value, item) in mapping.iter().enumerate() {
                            if item.is_invalid() {
                                write!(f, " exclude {value}")?;
                            }
                        }
                    }
                }

                if let Some(bits) = bits {
                    write!(f, " [bits: {bits:?}]")?;
                }
            },
            PartMapping::MemoryComputation {
                mapping, ..
            } => {
                for (key, value) in mapping.iter().enumerate() {
                    if key != 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{:0pad$b} => ", key, pad = self.size)?;
                    if let Some(computation) = value {
                        if key as u64 == self.value {
                            write!(f, "[ {} ]", computation.display(ARG_NAMES))?;
                        } else {
                            write!(f, "{}", computation.display(ARG_NAMES))?;
                        }
                    } else {
                        write!(f, "-")?;
                    }
                }
            },
        }

        Ok(())
    }
}

impl<A: Arch> Display for Part<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{} bits]: {}",
            self.size,
            DisplayPartMapping {
                mapping: &self.mapping,
                value: self.value,
                size: self.size,
            }
        )
    }
}
