use std::ops::Index;

use arrayvec::ArrayVec;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AttemptedParse<T, RawValue> {
    Ok(T),
    InvalidValue(RawValue),
}

impl<T, RawValue> AttemptedParse<T, RawValue> {
    pub fn is_invalid(&self) -> bool {
        matches!(self, AttemptedParse::InvalidValue(_))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Rex {
    pub w: bool,
    pub r: bool,
    pub x: bool,
    pub b: bool,
}

/// The two byte VEX prefix C5 ..
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Vex2 {
    pub p: Option<SimplePrefix>,
    pub l: bool,
    pub v: u8,
    pub r: bool,
}

/// The three-byte VEX prefixe C4 .. ..
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Vex3 {
    pub p: Option<SimplePrefix>,
    pub l: bool,
    pub v: u8,
    pub m: AttemptedParse<OpcodeMap, u8>,
    pub rex: Rex,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum SimplePrefix {
    /// F0
    Lock,
    /// F2
    Repnz,
    /// F3
    Repz,
    /// 2E -- can also be a branch not taken hint.
    OverrideCS,
    /// 36
    OverrideSS,
    /// 3E -- can also be a branch taken hint
    OverrideDS,
    /// 26
    OverrideES,
    /// 64
    OverrideFS,
    /// 65
    OverrideGS,
    /// 66
    DataSizeOverride,
    /// 67
    AddrSizeOverride,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Prefix {
    Simple(SimplePrefix),
    OpcodeMap(OpcodeMap),
    Rex(Rex),
    Vex2(Vex2),
    Vex3(Vex3),
    IncompleteVex2,
    IncompleteVex3,
    Xop,
    BrokenXop,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum OpcodeMap {
    Default,
    Map0F,
    Map0F38,
    Map0F3A,
}

pub struct ParsedInstructionPrefixes {
    prefixes: ArrayVec<Prefix, 15>,
}

impl ParsedInstructionPrefixes {
    pub fn parse(mut instr: &[u8]) -> (ParsedInstructionPrefixes, &[u8]) {
        let mut parsed = ParsedInstructionPrefixes {
            prefixes: ArrayVec::new(),
        };

        while parsed.effective_opcode_map() == Some(OpcodeMap::Default) {
            instr = match instr {
                [0x0F, 0x38, ..] => {
                    parsed.prefixes.push(Prefix::OpcodeMap(OpcodeMap::Map0F38));
                    &instr[2..]
                },
                [0x0F, 0x3A, ..] => {
                    parsed.prefixes.push(Prefix::OpcodeMap(OpcodeMap::Map0F3A));
                    &instr[2..]
                },
                [0x0F, ..] => {
                    parsed.prefixes.push(Prefix::OpcodeMap(OpcodeMap::Map0F));
                    &instr[1..]
                },

                [0x2E, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::OverrideCS));
                    &instr[1..]
                },
                [0x36, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::OverrideSS));
                    &instr[1..]
                },
                [0x3E, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::OverrideDS));
                    &instr[1..]
                },
                [0x26, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::OverrideES));
                    &instr[1..]
                },
                [0x64, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::OverrideFS));
                    &instr[1..]
                },
                [0x65, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::OverrideGS));
                    &instr[1..]
                },

                [0x66, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::DataSizeOverride));
                    &instr[1..]
                },
                [0x67, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::AddrSizeOverride));
                    &instr[1..]
                },
                [0xF0, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::Lock));
                    &instr[1..]
                },
                [0xF2, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::Repnz));
                    &instr[1..]
                },
                [0xF3, ..] => {
                    parsed.prefixes.push(Prefix::Simple(SimplePrefix::Repz));
                    &instr[1..]
                },
                // We're not parsing the xop prefix itself, because practically nobody uses it.
                [0x8F, c, ..] if c & 0b1_1111 >= 8 => {
                    parsed.prefixes.push(Prefix::Xop);
                    &instr[1..]
                },
                [0x8F, c, ..] if [0x20, 0x60, 0xA0, 0xE0].contains(&(c & 0xf0)) => {
                    parsed.prefixes.push(Prefix::BrokenXop);
                    &instr[1..]
                },
                [rex, ..] if rex & 0xf0 == 0x40 => {
                    parsed.prefixes.push(Prefix::Rex(Rex {
                        w: instr[0] & 0x8 > 0,
                        r: instr[0] & 0x4 > 0,
                        x: instr[0] & 0x2 > 0,
                        b: instr[0] & 0x1 > 0,
                    }));

                    &instr[1..]
                },
                [0xC4, c1, c2, ..] => {
                    let p = match c2 & 0b11 {
                        0 => None,
                        1 => Some(SimplePrefix::Lock),
                        2 => Some(SimplePrefix::Repnz),
                        3 => Some(SimplePrefix::Repz),
                        _ => unreachable!(),
                    };

                    let rex = Rex {
                        r: c1 & 0x80 == 0,
                        w: c2 & 0x80 != 0,
                        x: c1 & 0x40 == 0,
                        b: c1 & 0x20 == 0,
                    };

                    let opcode = match c1 & 0b11111 {
                        1 => AttemptedParse::Ok(OpcodeMap::Map0F),
                        2 => AttemptedParse::Ok(OpcodeMap::Map0F38),
                        3 => AttemptedParse::Ok(OpcodeMap::Map0F3A),
                        // Does not exist (officially)
                        val => AttemptedParse::InvalidValue(val),
                    };

                    parsed.prefixes.push(Prefix::Vex3(Vex3 {
                        p,
                        l: (c2 & 0b100) != 0,
                        v: ((c2 & 0b0111_1000) >> 3) ^ 0b1111,
                        m: opcode,
                        rex,
                    }));

                    &instr[3..]
                },
                [0xC4, ..] => {
                    parsed.prefixes.push(Prefix::IncompleteVex3);
                    return (parsed, &instr[1..]);
                },
                // Two-byte VEX
                [0xC5, c, ..] => {
                    let p = match c & 0b11 {
                        0 => None,
                        1 => Some(SimplePrefix::Lock),
                        2 => Some(SimplePrefix::Repnz),
                        3 => Some(SimplePrefix::Repz),
                        _ => unreachable!(),
                    };

                    parsed.prefixes.push(Prefix::Vex2(Vex2 {
                        r: c & 0b1000_0000 == 0,
                        p,
                        l: c & 0b100 != 0,
                        v: ((c & 0b0111_1000) >> 3) ^ 0b1111,
                    }));

                    &instr[2..]
                },
                [0xC5, ..] => {
                    parsed.prefixes.push(Prefix::IncompleteVex2);
                    return (parsed, &instr[1..]);
                },
                // TODO: EVEX, XOP
                _ => break,
            };
        }

        (parsed, instr)
    }

    pub fn effective_opcode_map(&self) -> Option<OpcodeMap> {
        self.prefixes
            .iter()
            .try_fold(OpcodeMap::Default, |acc, &prefix| match prefix {
                Prefix::OpcodeMap(map) => Some(map),
                Prefix::Vex2(_) | Prefix::IncompleteVex2 | Prefix::IncompleteVex3 => Some(OpcodeMap::Map0F),
                Prefix::Vex3(v) => match v.m {
                    AttemptedParse::Ok(map) => Some(map),
                    AttemptedParse::InvalidValue(_) => None,
                },
                _ => Some(acc),
            })
    }

    pub fn prefixes(&self) -> &[Prefix] {
        &self.prefixes
    }
}

impl Index<usize> for ParsedInstructionPrefixes {
    type Output = Prefix;

    fn index(&self, index: usize) -> &Self::Output {
        &self.prefixes[index]
    }
}

#[cfg(test)]
mod tests {
    use super::{AttemptedParse, OpcodeMap, ParsedInstructionPrefixes, Prefix, Rex, SimplePrefix, Vex2, Vex3};

    fn parse(instr: &[u8]) -> (Vec<Prefix>, &[u8]) {
        let (parsed, rest) = ParsedInstructionPrefixes::parse(instr);
        (parsed.prefixes().to_vec(), rest)
    }

    #[test]
    pub fn test_prefix_parsing() {
        assert_eq!(
            parse(&[0x0f, 0x05]),
            (vec![Prefix::OpcodeMap(OpcodeMap::Map0F)], [0x05].as_ref())
        );
        assert_eq!(
            parse(&[0x40, 0xc5, 0x00, 0x48]),
            (
                vec![
                    Prefix::Rex(Rex {
                        w: false,
                        r: false,
                        x: false,
                        b: false,
                    }),
                    Prefix::Vex2(Vex2 {
                        p: None,
                        l: false,
                        v: 0b1111,
                        r: true,
                    })
                ],
                [0x48].as_ref()
            )
        );
        assert_eq!(
            parse(&[0xC4, 0x00, 0x67, 0xC5, 0x34, 0xC5, 0x00, 0x00, 0x04, 0x00]),
            (
                vec![Prefix::Vex3(Vex3 {
                    p: Some(SimplePrefix::Repz),
                    l: true,
                    v: 3,
                    m: AttemptedParse::InvalidValue(0),
                    rex: Rex {
                        w: false,
                        r: true,
                        x: true,
                        b: true,
                    }
                })],
                [0xC5, 0x34, 0xC5, 0x00, 0x00, 0x04, 0x00].as_ref()
            )
        );
    }
}
