use std::fmt::Debug;

use super::{ByteFilter, InstructionFilter};
use crate::instr::{FilterBit, Instruction};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Node {
    Branch { is_0: NodeIndex, is_1: NodeIndex },
    Ignore { next: NodeIndex },
}

// TODO: Just use an U64
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct U40(u8, u32);

impl U40 {
    pub fn new(val: u64) -> U40 {
        assert!(val <= 0x00ff_ffff_ffff);
        U40((val >> 32) as u8, val as u32)
    }

    pub fn value(&self) -> u64 {
        self.1 as u64 | ((self.0 as u64) << 32)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum NodeIndex {
    Enumerate,
    Skip,
    Index(U40),
}

impl NodeIndex {
    pub fn unwrap(self) -> usize {
        match self.index() {
            Some(index) => index,
            None => panic!("Tried to unwrap a leaf node"),
        }
    }

    pub fn index(&self) -> Option<usize> {
        match self {
            NodeIndex::Enumerate | NodeIndex::Skip => None,
            NodeIndex::Index(index) => Some(index.value() as usize),
        }
    }
}

#[derive(Copy, Clone)]
struct NodeRef<'t> {
    index: NodeIndex,
    tree: &'t FilterTree,
}

impl Debug for NodeRef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.node().fmt(f)
    }
}

#[derive(Copy, Clone, Debug)]
enum NodeRefData<'t> {
    Branch { is_0: NodeRef<'t>, is_1: NodeRef<'t> },
    Ignore { next: NodeRef<'t> },
    Enumerate,
    Skip,
}

impl<'t> NodeRef<'t> {
    pub fn node(&self) -> NodeRefData<'t> {
        match self.index {
            NodeIndex::Enumerate => NodeRefData::Enumerate,
            NodeIndex::Skip => NodeRefData::Skip,
            NodeIndex::Index(index) => match self.tree.entries[index.value() as usize] {
                Node::Branch {
                    is_0,
                    is_1,
                } => NodeRefData::Branch {
                    is_0: self.node_from_tree(is_0),
                    is_1: self.node_from_tree(is_1),
                },
                Node::Ignore {
                    next,
                } => NodeRefData::Ignore {
                    next: self.node_from_tree(next),
                },
            },
        }
    }

    fn node_from_tree(&self, index: NodeIndex) -> NodeRef<'t> {
        NodeRef {
            index,
            tree: self.tree,
        }
    }

    fn debug_print<W: std::fmt::Write>(&self, f: &mut W, prefix: &str) -> std::fmt::Result {
        match self.node() {
            NodeRefData::Branch {
                is_0,
                is_1,
            } => {
                write!(f, "┬─ 0 ─")?;
                is_0.debug_print(f, &format!("{prefix}│     "))?;
                writeln!(f)?;
                write!(f, "{prefix}└─ 1 ─")?;
                is_1.debug_print(f, &format!("{prefix}      "))?;
            },
            NodeRefData::Ignore {
                next,
            } => {
                write!(f, "─ _ ─")?;
                next.debug_print(f, &format!("{prefix}     "))?;
            },
            NodeRefData::Enumerate => write!(f, "🭬enumerate")?,
            NodeRefData::Skip => write!(f, "🭬skip")?,
        }

        Ok(())
    }
}

impl PartialEq for NodeRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        if std::ptr::eq(self.tree, other.tree) {
            // Optimization: if both refer to the same tree, we can just compare indexes
            match (self.index, other.index) {
                (NodeIndex::Enumerate, NodeIndex::Enumerate) | (NodeIndex::Skip, NodeIndex::Skip) => true,
                (NodeIndex::Index(lhs), NodeIndex::Index(rhs)) => {
                    lhs == rhs || self.tree.entries[lhs.value() as usize] == other.tree.entries[rhs.value() as usize]
                },
                _ => false,
            }
        } else {
            self.node() == other.node()
        }
    }
}

impl PartialEq for NodeRefData<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Branch {
                    is_0: left0,
                    is_1: left1,
                },
                Self::Branch {
                    is_0: right0,
                    is_1: right1,
                },
            ) => left0.node() == right0.node() && left1.node() == right1.node(),
            (
                Self::Ignore {
                    next: left,
                },
                Self::Ignore {
                    next: right,
                },
            ) => left.node() == right.node(),
            (Self::Enumerate, Self::Enumerate) | (Self::Skip, Self::Skip) => true,
            _ => false,
        }
    }
}

/// A tree-structure that can efficiently determine whether an instruction is covered by a large set of filters.
pub struct FilterTree {
    entries: Vec<Node>,
    empty: Vec<usize>,
}

impl FilterTree {
    /// Creates an empty [`FilterTree`].
    pub fn new() -> FilterTree {
        FilterTree {
            entries: vec![Node::Ignore {
                next: NodeIndex::Enumerate,
            }],
            empty: Vec::new(),
        }
    }

    fn root(&self) -> NodeRef {
        NodeRef {
            index: NodeIndex::Index(U40::new(0)),
            tree: self,
        }
    }

    /// Returns the number of tree nodes in use.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len() - self.empty.len()
    }

    /// Returns true if the tree has no nodes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of nodes in use in the tree.
    /// Counts all nodes recursively.
    pub fn count_nodes(&self) -> usize {
        let mut queue = Vec::new();
        let mut count = 0;
        queue.push(self.root());
        while let Some(node) = queue.pop() {
            count += 1;
            match node.node() {
                NodeRefData::Branch {
                    is_0,
                    is_1,
                } => {
                    queue.push(is_0);
                    queue.push(is_1);
                },
                NodeRefData::Ignore {
                    next,
                } => queue.push(next),
                NodeRefData::Enumerate => (),
                NodeRefData::Skip => (),
            }
        }

        count
    }

    fn new_node(&mut self, node: Node) -> NodeIndex {
        NodeIndex::Index(if let Some(index) = self.empty.pop() {
            self.entries[index] = node;
            U40::new(index as u64)
        } else {
            let index = self.entries.len();
            self.entries.push(node);
            U40::new(index as u64)
        })
    }

    fn free_entry(&mut self, index: usize) {
        if index == self.entries.len() - 1 {
            self.entries.pop();
        } else {
            self.empty.push(index);
        }
    }

    fn free_node(&mut self, index: NodeIndex) {
        if let NodeIndex::Index(index) = index {
            match self.entries[index.value() as usize] {
                Node::Branch {
                    is_0,
                    is_1,
                } => {
                    self.free_node(is_0);
                    self.free_node(is_1);
                },
                Node::Ignore {
                    next,
                } => {
                    self.free_node(next);
                },
            }

            self.free_entry(index.value() as usize);
        }
    }

    fn deep_clone_node(&mut self, index: NodeIndex) -> NodeIndex {
        match index {
            NodeIndex::Enumerate => NodeIndex::Enumerate,
            NodeIndex::Skip => NodeIndex::Skip,
            NodeIndex::Index(index) => match self.entries[index.value() as usize] {
                Node::Branch {
                    is_0,
                    is_1,
                } => {
                    let is_0 = self.deep_clone_node(is_0);
                    let is_1 = self.deep_clone_node(is_1);
                    self.new_node(Node::Branch {
                        is_0,
                        is_1,
                    })
                },
                Node::Ignore {
                    next,
                } => {
                    let next = self.deep_clone_node(next);
                    self.new_node(Node::Ignore {
                        next,
                    })
                },
            },
        }
    }

    fn node_to_index(&mut self, node: NodeIndex, update: impl FnOnce(&mut Self, NodeIndex)) -> Option<usize> {
        match node {
            NodeIndex::Enumerate => {
                let new = self.new_node(Node::Ignore {
                    next: NodeIndex::Enumerate,
                });

                update(self, new);

                Some(new.unwrap())
            },
            NodeIndex::Skip => None,
            NodeIndex::Index(index) => Some(index.value() as usize),
        }
    }

    fn add_internal(&mut self, mut cur_index: usize, filter: &InstructionFilter, filter_index: usize) -> bool {
        let mut modified = false;
        let real_len = {
            let mut len = filter.bit_len();
            while len > 1 && filter.nth_bit_from_left(len - 1) == FilterBit::Wildcard {
                len -= 1;
            }

            len
        };
        for n in filter_index..real_len {
            let last = n == real_len - 1;
            let bit = filter.nth_bit_from_left(n);
            if last {
                match self.entries[cur_index] {
                    Node::Branch {
                        is_0,
                        is_1,
                    } => match bit {
                        FilterBit::Is0 => {
                            if is_0 != NodeIndex::Skip {
                                modified = true;
                                self.free_node(is_0);
                                self.entries[cur_index] = Node::Branch {
                                    is_0: NodeIndex::Skip,
                                    is_1,
                                };
                            }
                        },
                        FilterBit::Is1 => {
                            if is_1 != NodeIndex::Skip {
                                modified = true;
                                self.free_node(is_1);
                                self.entries[cur_index] = Node::Branch {
                                    is_0,
                                    is_1: NodeIndex::Skip,
                                };
                            }
                        },
                        FilterBit::Wildcard => {
                            modified = true;
                            self.free_node(is_0);
                            self.free_node(is_1);
                            self.entries[cur_index] = Node::Ignore {
                                next: NodeIndex::Skip,
                            };
                        },
                    },
                    Node::Ignore {
                        next,
                    } => match bit {
                        FilterBit::Is0 => {
                            modified = true;
                            self.entries[cur_index] = Node::Branch {
                                is_0: NodeIndex::Skip,
                                is_1: next,
                            };
                        },
                        FilterBit::Is1 => {
                            modified = true;
                            self.entries[cur_index] = Node::Branch {
                                is_0: next,
                                is_1: NodeIndex::Skip,
                            };
                        },
                        FilterBit::Wildcard => {
                            if next != NodeIndex::Skip {
                                modified = true;
                                self.free_node(next);
                                self.entries[cur_index] = Node::Ignore {
                                    next: NodeIndex::Skip,
                                };
                            }
                        },
                    },
                }
            } else {
                match self.entries[cur_index] {
                    Node::Branch {
                        is_0,
                        is_1,
                    } => match bit {
                        FilterBit::Is0 => {
                            cur_index = match self.node_to_index(is_0, |me, new| {
                                me.entries[cur_index] = Node::Branch {
                                    is_0: new,
                                    is_1,
                                }
                            }) {
                                Some(index) => index,
                                None => return modified,
                            }
                        },
                        FilterBit::Is1 => {
                            cur_index = match self.node_to_index(is_1, |me, new| {
                                me.entries[cur_index] = Node::Branch {
                                    is_0,
                                    is_1: new,
                                }
                            }) {
                                Some(index) => index,
                                None => return modified,
                            }
                        },
                        FilterBit::Wildcard => {
                            if let Some(index) = self.node_to_index(is_0, |me, new| {
                                me.entries[cur_index] = Node::Branch {
                                    is_0: new,
                                    is_1,
                                }
                            }) {
                                modified |= self.add_internal(index, filter, n + 1)
                            }

                            if let Some(index) = self.node_to_index(is_1, |me, new| match &mut me.entries[cur_index] {
                                Node::Branch {
                                    is_1, ..
                                } => *is_1 = new,
                                _ => panic!(),
                            }) {
                                modified |= self.add_internal(index, filter, n + 1)
                            }

                            // println!("Branch wildcard processed for bit {n}: {self:?}");

                            return modified;
                        },
                    },
                    Node::Ignore {
                        next,
                    } => match bit {
                        bit @ (FilterBit::Is0 | FilterBit::Is1) => {
                            let is_0 = next;
                            let is_1 = self.deep_clone_node(next);
                            self.entries[cur_index] = Node::Branch {
                                is_0,
                                is_1,
                            };

                            modified = true;
                            cur_index = match bit {
                                FilterBit::Is0 => match self.node_to_index(is_0, |me, new| {
                                    me.entries[cur_index] = Node::Branch {
                                        is_0: new,
                                        is_1,
                                    }
                                }) {
                                    Some(index) => index,
                                    None => return modified,
                                },
                                FilterBit::Is1 => match self.node_to_index(is_1, |me, new| {
                                    me.entries[cur_index] = Node::Branch {
                                        is_0,
                                        is_1: new,
                                    }
                                }) {
                                    Some(index) => index,
                                    None => return modified,
                                },
                                _ => unreachable!(),
                            };
                        },
                        FilterBit::Wildcard => {
                            cur_index = match self.node_to_index(next, |me, new| {
                                me.entries[cur_index] = Node::Ignore {
                                    next: new,
                                }
                            }) {
                                Some(index) => index,
                                None => return modified,
                            }
                        },
                    },
                }
            }
        }

        modified
    }

    /// Inserts the filter into the tree
    pub fn filter(&mut self, filter: &InstructionFilter) {
        // println!("Adding filter to tree: {:?}", filter);
        if self.add_internal(0, filter, 0) {
            // println!("Before optimize: {self:?}");
            if let Some(index) = self.optimize(NodeIndex::Index(U40::new(0)), filter, 0) {
                match index {
                    NodeIndex::Enumerate | NodeIndex::Skip => {
                        self.empty.clear();
                        self.entries.clear();
                        self.entries.push(Node::Ignore {
                            next: index,
                        });
                    },
                    NodeIndex::Index(index) => {
                        self.entries[0] = self.entries[index.value() as usize];
                        self.free_entry(index.value() as usize);
                    },
                }
            }
        }
    }

    /// Prunes the tree, removing matches before or furthest away from `instruction`.
    /// This operation reduces the memory used for the tree.
    pub fn prune(&mut self, instruction: &Instruction) {
        let mut cur_index = NodeIndex::Index(U40::new(0));
        for bit in 0..instruction.bit_len() {
            let bit = instruction.nth_bit_from_left(bit);
            match cur_index {
                NodeIndex::Enumerate | NodeIndex::Skip => (),
                NodeIndex::Index(index) => match &mut self.entries[index.value() as usize] {
                    Node::Branch {
                        is_0,
                        is_1,
                    } => {
                        if bit == 0 {
                            match is_1 {
                                NodeIndex::Enumerate | NodeIndex::Skip => cur_index = *is_0,
                                node @ NodeIndex::Index(_) => {
                                    let tmp = *node;
                                    *node = NodeIndex::Enumerate;
                                    self.free_node(tmp);
                                    return
                                },
                            }
                        } else {
                            match is_0 {
                                NodeIndex::Enumerate | NodeIndex::Skip => cur_index = *is_1,
                                node @ NodeIndex::Index(_) => {
                                    let tmp = *node;
                                    *node = NodeIndex::Enumerate;
                                    self.free_node(tmp);
                                    return
                                },
                            }
                        }
                    },
                    Node::Ignore {
                        next,
                    } => cur_index = *next,
                },
            }
        }
    }

    /// Filters all instruction below `below`.
    pub fn filter_below(&mut self, below: &Instruction) {
        for i in 0..below.bit_len() {
            let instr0 = below.with_nth_bit_from_right(i, 0).with_rightmost_bits(i, 0);
            let instr1 = below.with_nth_bit_from_right(i, 0).with_rightmost_bits(i, 1);
            // println!("Instr: {:?}-{:?}", instr0, instr1);
            if &instr1 < below {
                let filter = InstructionFilter::new(
                    instr0
                        .bytes()
                        .iter()
                        .copied()
                        .rev()
                        .enumerate()
                        .map(|(index, b)| {
                            let bits_to_mask = i.saturating_sub(index * 8) as u32;
                            ByteFilter::new(0xffu8.checked_shl(bits_to_mask).unwrap_or(0), b)
                        })
                        .rev(),
                );

                self.filter(&filter);
            }
        }
    }

    /// Filters all instruction above `start`.
    pub fn filter_above(&mut self, start: &Instruction) {
        for i in 0..start.bit_len() {
            let instr0 = start.with_nth_bit_from_right(i, 1).with_rightmost_bits(i, 0);
            // println!("Instr: {:?}-{:?}", instr0, instr1);
            if &instr0 > start {
                let filter = InstructionFilter::new(
                    instr0
                        .bytes()
                        .iter()
                        .copied()
                        .rev()
                        .enumerate()
                        .map(|(index, b)| {
                            let bits_to_mask = i.saturating_sub(index * 8) as u32;
                            ByteFilter::new(0xffu8.checked_shl(bits_to_mask).unwrap_or(0), b)
                        })
                        .rev(),
                );

                self.filter(&filter);
            }
        }
    }

    fn optimize(&mut self, cur_index: NodeIndex, optimize_path: &InstructionFilter, filter_index: usize) -> Option<NodeIndex> {
        match cur_index {
            NodeIndex::Enumerate | NodeIndex::Skip => Some(cur_index),
            NodeIndex::Index(cur_index) => match self.entries[cur_index.value() as usize] {
                Node::Branch {
                    is_0,
                    is_1,
                } => {
                    let new_is_0 = match optimize_path.nth_bit_from_left(filter_index) {
                        FilterBit::Is0 | FilterBit::Wildcard => self.optimize(is_0, optimize_path, filter_index + 1),
                        FilterBit::Is1 => None,
                    };
                    let new_is_1 = match optimize_path.nth_bit_from_left(filter_index) {
                        FilterBit::Is1 | FilterBit::Wildcard => self.optimize(is_1, optimize_path, filter_index + 1),
                        FilterBit::Is0 => None,
                    };

                    let (is_0, is_1) = if new_is_0.is_some() || new_is_1.is_some() {
                        let is_0 = new_is_0.unwrap_or(is_0);
                        let is_1 = new_is_1.unwrap_or(is_1);
                        self.entries[cur_index.value() as usize] = Node::Branch {
                            is_0,
                            is_1,
                        };

                        (is_0, is_1)
                    } else {
                        (is_0, is_1)
                    };

                    if (NodeRef {
                        index: is_0,
                        tree: self,
                    } == NodeRef {
                        index: is_1,
                        tree: self,
                    }) {
                        match is_0 {
                            NodeIndex::Enumerate | NodeIndex::Skip => {
                                self.free_node(is_1);
                                self.free_entry(cur_index.value() as usize);
                                Some(is_0)
                            },
                            NodeIndex::Index(_) => {
                                self.entries[cur_index.value() as usize] = Node::Ignore {
                                    next: is_0,
                                };
                                self.free_node(is_1);

                                None
                            },
                        }
                    } else {
                        None
                    }
                },
                Node::Ignore {
                    next,
                } => {
                    if let Some(next) = self.optimize(next, optimize_path, filter_index + 1) {
                        match next {
                            NodeIndex::Enumerate | NodeIndex::Skip => {
                                self.free_entry(cur_index.value() as usize);

                                Some(next)
                            },
                            index @ NodeIndex::Index(_) => {
                                self.entries[cur_index.value() as usize] = Node::Ignore {
                                    next: index,
                                };

                                None
                            },
                        }
                    } else {
                        None
                    }
                },
            },
        }
    }

    fn find_next_internal(node: NodeRef, bit_index: usize, path: &mut Instruction) -> bool {
        // println!("find next (bit {}): {:?}", bit_index, path);
        match node.node() {
            NodeRefData::Branch {
                is_0,
                is_1,
            } => {
                if bit_index >= path.bit_len() {
                    *path = path.extend();
                    // println!("Extended: {:?}", path);
                }

                if path.nth_bit_from_left(bit_index) == 0 && Self::find_next_internal(is_0, bit_index + 1, path) {
                    true
                } else {
                    if path.nth_bit_from_left(bit_index) == 0 {
                        *path = path.with_nth_bit_from_left(bit_index, 1).resize(bit_index / 8 + 1, 0x00);
                    }

                    if Self::find_next_internal(is_1, bit_index + 1, path) {
                        true
                    } else {
                        *path = path.with_nth_bit_from_left(bit_index, 0).resize(bit_index / 8 + 1, 0x00);
                        false
                    }
                }
            },
            NodeRefData::Ignore {
                next,
            } => {
                if bit_index >= path.bit_len() {
                    *path = path.extend();
                    // println!("Extended: {:?}", path);
                }

                if Self::find_next_internal(next, bit_index + 1, path) {
                    true
                } else {
                    if path.nth_bit_from_left(bit_index) == 0 {
                        // println!("Trying bit {} = 1", bit_index);
                        *path = path.with_nth_bit_from_left(bit_index, 1).resize(bit_index / 8 + 1, 0x00);
                        if Self::find_next_internal(next, bit_index + 1, path) {
                            return true;
                        }
                    }

                    *path = path.with_nth_bit_from_left(bit_index, 0).resize(bit_index / 8 + 1, 0x00);
                    false
                }
            },
            NodeRefData::Enumerate => {
                // println!("Enumerate!");
                true
            },
            NodeRefData::Skip => {
                // println!("Skip!");
                if bit_index < path.bit_len() {
                    *path = path.with_rightmost_bits(path.bit_len() - bit_index, 0);
                }

                false
            },
        }
    }

    /// Returns the (lexicographically) next instruction not matched by any filter.
    pub fn find_next(&self, instr: &Instruction) -> Option<Instruction> {
        let mut next = *instr;
        if Self::find_next_internal(self.root(), 0, &mut next) {
            Some(next)
        } else {
            None
        }
    }

    fn covers_internal(&self, mut cur_index: usize, filter: &InstructionFilter, filter_index: usize) -> bool {
        let real_len = {
            let mut len = filter.bit_len();
            while len > 1 && filter.nth_bit_from_left(len - 1) == FilterBit::Wildcard {
                len -= 1;
            }

            len
        };
        for n in filter_index..real_len {
            let bit = filter.nth_bit_from_left(n);
            match self.entries[cur_index] {
                Node::Branch {
                    is_0,
                    is_1,
                } => match bit {
                    FilterBit::Is0 => match is_0 {
                        NodeIndex::Enumerate => return false,
                        NodeIndex::Skip => return true,
                        NodeIndex::Index(index) => cur_index = index.value() as usize,
                    },
                    FilterBit::Is1 => match is_1 {
                        NodeIndex::Enumerate => return false,
                        NodeIndex::Skip => return true,
                        NodeIndex::Index(index) => cur_index = index.value() as usize,
                    },
                    FilterBit::Wildcard => {
                        return match is_0 {
                            NodeIndex::Enumerate => false,
                            NodeIndex::Skip => true,
                            NodeIndex::Index(index) => {
                                if !self.covers_internal(index.value() as usize, filter, n + 1) {
                                    false
                                } else {
                                    match is_1 {
                                        NodeIndex::Enumerate => false,
                                        NodeIndex::Skip => true,
                                        NodeIndex::Index(index) => self.covers_internal(index.value() as usize, filter, n + 1),
                                    }
                                }
                            },
                        }
                    },
                },
                Node::Ignore {
                    next,
                } => match next {
                    NodeIndex::Enumerate => return false,
                    NodeIndex::Skip => return true,
                    NodeIndex::Index(index) => cur_index = index.value() as usize,
                },
            }
        }

        false
    }

    /// Returns true if the tree fully covers all instructions matched by the filter.
    pub fn covers(&self, filter: &InstructionFilter) -> bool {
        self.covers_internal(0, filter, 0)
    }
}

impl Default for FilterTree {
    fn default() -> Self {
        Self::new()
    }
}

impl PartialEq for FilterTree {
    fn eq(&self, other: &Self) -> bool {
        self.root() == other.root()
    }
}

impl Debug for FilterTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "FilterTree {{")?;
        write!(f, " 🮮 ─")?;
        self.root().debug_print(f, "    ")?;
        writeln!(f)?;
        writeln!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::FilterTree;
    use crate::instr::tree::{Node, U40};
    use crate::instr::{ByteFilter, Instruction, InstructionFilter};

    #[test]
    pub fn gc_working1() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000"));
        println!("{tree:?}");
        tree.filter(&InstructionFilter::parse("0000___1"));
        println!("{tree:?}");
        tree.filter(&InstructionFilter::parse("0000__1_"));
        println!("{tree:?}");
        tree.filter(&InstructionFilter::parse("0000_1__"));
        println!("{tree:?}");
        tree.filter(&InstructionFilter::parse("00001___"));
        println!("{tree:?}");
        tree.filter(&InstructionFilter::parse("________"));
        println!("{tree:?}");

        assert_eq!(tree.len(), 1, "Tree: {tree:?}");
    }

    #[test]
    pub fn gc_working2() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000"));
        tree.filter(&InstructionFilter::parse("0000___1"));
        tree.filter(&InstructionFilter::parse("0000__1_"));
        tree.filter(&InstructionFilter::parse("0000_1__"));
        tree.filter(&InstructionFilter::parse("00001___"));
        tree.filter(&InstructionFilter::parse("0_______"));

        assert_eq!(tree.len(), 1);
    }

    #[test]
    pub fn gc_working3() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000 00000000"));
        tree.filter(&InstructionFilter::parse("00000000 0000___1"));
        tree.filter(&InstructionFilter::parse("00000000 0000__1_"));
        tree.filter(&InstructionFilter::parse("00000000 0000_1__"));
        tree.filter(&InstructionFilter::parse("00000000 00001___"));
        tree.filter(&InstructionFilter::parse("00000000 ________"));

        println!("Tree: {tree:?}");

        assert_eq!(tree.len(), 8);
    }

    #[test]
    pub fn simple_find_next() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("0000__1_"));

        println!("{tree:?}");

        assert_eq!(tree.find_next(&Instruction::new(&[0x02])), Some(Instruction::new(&[0x04])));
        assert_eq!(tree.find_next(&Instruction::new(&[0x06])), Some(Instruction::new(&[0x08])));
    }

    #[test]
    pub fn find_next_carry() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00001111 00010111"));
        assert_eq!(
            tree.find_next(&Instruction::new(&[0x0f, 0x17])),
            Some(Instruction::new(&[0x0f, 0x18]))
        );
    }

    #[test]
    pub fn find_next_carry2() {
        let mut tree = FilterTree::new();
        for i in 0..8 {
            tree.filter(&InstructionFilter::new(vec![
                ByteFilter::new(0b0010_0001, 0),
                ByteFilter::new(0b1111_1111, 0),
                ByteFilter::new(0b1111_1111, 0),
                ByteFilter::new(1 << i, 1 << i),
            ]));
        }
        assert_eq!(
            tree.find_next(&Instruction::new(&[0x00, 0x00, 0x00, 0x01])),
            Some(Instruction::new(&[0x00, 0x00, 0x01,]))
        );
    }

    #[test]
    pub fn filtering_nothing() {
        let tree = FilterTree::new();
        assert_eq!(tree.find_next(&Instruction::new(&[0x00])), Some(Instruction::new(&[0x00])));
    }

    #[test]
    pub fn filtering_concrete() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000"));
        assert_eq!(tree.find_next(&Instruction::new(&[0x00])), Some(Instruction::new(&[0x01])));
    }

    #[test]
    pub fn filter_below() {
        let mut tree = FilterTree::new();
        tree.filter_below(&Instruction::new(&[0xab, 0xcd]));
        assert_eq!(
            tree.find_next(&Instruction::new(&[0x00])),
            Some(Instruction::new(&[0xab, 0xcd]))
        );
        assert_eq!(
            tree.find_next(&Instruction::new(&[0xab, 0x00])),
            Some(Instruction::new(&[0xab, 0xcd]))
        );
        assert_eq!(
            tree.find_next(&Instruction::new(&[0xab, 0xce])),
            Some(Instruction::new(&[0xab, 0xce]))
        );
    }

    #[test]
    pub fn filter_above() {
        let mut tree = FilterTree::new();
        tree.filter_above(&Instruction::new(&[0xab, 0xcd]));
        assert_eq!(tree.find_next(&Instruction::new(&[0x00])), Some(Instruction::new(&[0x00])));
        assert_eq!(
            tree.find_next(&Instruction::new(&[0xab, 0x00])),
            Some(Instruction::new(&[0xab, 0x00]))
        );
        assert_eq!(tree.find_next(&Instruction::new(&[0xab, 0xce])), None);
        assert_eq!(tree.find_next(&Instruction::new(&[0xac])), None);
    }

    #[test]
    pub fn filter_folding() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00_____0"));
        tree.filter(&InstructionFilter::parse("00__1___"));
        tree.filter(&InstructionFilter::parse("00____1_"));
        tree.filter(&InstructionFilter::parse("0_____1_"));
        tree.filter(&InstructionFilter::parse("1____10_"));
        tree.filter(&InstructionFilter::parse("000___0_"));

        println!("Tree: {tree:?}");
    }

    #[test]
    pub fn filtering_wildcard() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("0000____"));
        assert_eq!(tree.find_next(&Instruction::new(&[0x00])), Some(Instruction::new(&[0x10])));
    }

    #[test]
    pub fn filtering_reduce() {
        let mut tree = FilterTree::new();
        for n in 0..=0xff {
            tree.filter(&InstructionFilter::new(vec![
                ByteFilter::new(0xff, 0x46),
                ByteFilter::new(0xff, n),
            ]));
        }
        tree.filter_above(&Instruction::new(&[0x47, 0x19, 0x1B]));
        assert_eq!(
            tree.find_next(&Instruction::new(&[0x46, 0x00])),
            Some(Instruction::new(&[0x47, 0x00]))
        );
    }

    #[test]
    pub fn filtering_end() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("1111____"));
        assert_eq!(tree.find_next(&Instruction::new(&[0xf0])), None);
    }

    #[test]
    pub fn filtering_must_return_unfiltered_next() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000"));
        tree.filter(&InstructionFilter::parse("00000001"));
        tree.filter(&InstructionFilter::parse("0000001_"));
        tree.filter(&InstructionFilter::parse("000001__"));
        tree.filter(&InstructionFilter::parse("00001___"));
        tree.filter(&InstructionFilter::parse("0001___0"));
        assert_eq!(tree.find_next(&Instruction::new(&[0x00])), Some(Instruction::new(&[0x11])));
    }

    #[test]
    pub fn filtering_folding_wildcards() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000"));
        tree.filter(&InstructionFilter::parse("0000___1"));
        tree.filter(&InstructionFilter::parse("0000__1_"));
        tree.filter(&InstructionFilter::parse("0000_1__"));
        tree.filter(&InstructionFilter::parse("00001___"));
        println!("Tree: {tree:?}");
        assert_eq!(tree.find_next(&Instruction::new(&[0x00])), Some(Instruction::new(&[0x10])));
    }

    #[test]
    pub fn filtering_complex_wildcards() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ________ 1_______ _____00_ 0_______",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00______ _1___0__ ________ 1_______",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 00000000 ________ _1______ ______1_ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00______ _____0__ ________ ____0___",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ________ ________ _______0 ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ________ ________ ___1_1__ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00______ 11___0__ _____00_ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 00000000 00______ _____0__ ___0____ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00______ ________ _0______ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ________ ______1_ _10_____ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ________ _1______ 1_______ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ________ _______1 ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00______ ______0_ ________ __0_____",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ________ _____1__ _1______ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ________ 1_______ 1____0__ 1_______",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ________ 1_______ 1____00_ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00______ ________ ________ __0_0___",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 00000000 00______ _1_1_0__ ___1____ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 00000000 00______ 1__1____ 1__1_0__ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00______ ___1____ ________ __0_____",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00______ _____00_ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ______1_ ________ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 ___0____ _____0__ ________ 0___1___",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00_0____ _____0__ ________ 0_______",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 0__00000 ________ _0______ __1_____ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 _______0 ______0_ 0____0__ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 _______0 ________ 0____0__ 0_______",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00_0____ _1___0__ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 00_0____ 1____0__ 1____0__ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "01100110 1111011_ 10110100 ___00000 _______0 11______ __0_____ ________",
        ));

        println!("Tree: {tree:?}");
        assert_eq!(
            tree.find_next(&Instruction::new(&[0x66, 0xf6, 0xb4, 0x00, 0x00, 0x00, 0x00, 0x00])),
            Some(Instruction::new(&[0x66, 0xf6, 0xb4, 0x00, 0x11, 0x42, 0x71, 0x08]))
        );
    }

    #[test]
    pub fn add_concrete_filter() {
        use Node::*;

        use super::NodeIndex::*;

        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000"));
        assert_eq!(
            tree,
            FilterTree {
                entries: vec![
                    Branch {
                        is_0: Index(U40::new(1)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(2)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(3)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(4)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(5)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(6)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(7)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Skip,
                        is_1: Enumerate
                    },
                ],
                empty: Vec::new()
            }
        );
    }

    #[test]
    pub fn add_filter_with_wildcards() {
        use Node::*;

        use super::NodeIndex::*;

        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("0000000_"));
        assert_eq!(
            tree,
            FilterTree {
                entries: vec![
                    Branch {
                        is_0: Index(U40::new(1)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(2)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(3)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(4)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(5)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(6)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Skip,
                        is_1: Enumerate
                    },
                ],
                empty: Vec::new(),
            }
        );
    }

    #[test]
    pub fn add_filters_that_fold() {
        use Node::*;

        use super::NodeIndex::*;

        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000"));
        tree.filter(&InstructionFilter::parse("00001011"));
        tree.filter(&InstructionFilter::parse("0000_100"));
        println!("{tree:?}");

        assert_eq!(
            tree,
            dbg!(FilterTree {
                entries: vec![
                    Branch {
                        is_0: Index(U40::new(1)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(2)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(3)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(4)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(5)),
                        is_1: Index(U40::new(8))
                    },
                    Branch {
                        is_0: Index(U40::new(6)),
                        is_1: Index(U40::new(11))
                    },
                    Branch {
                        is_0: Index(U40::new(7)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Skip,
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(9)),
                        is_1: Index(U40::new(11))
                    },
                    Branch {
                        is_0: Enumerate,
                        is_1: Index(U40::new(10))
                    },
                    Branch {
                        is_0: Enumerate,
                        is_1: Skip
                    },
                    Branch {
                        is_0: Index(U40::new(12)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Skip,
                        is_1: Enumerate
                    },
                ],
                empty: Vec::new(),
            })
        );
    }

    #[test]
    pub fn add_splitting_filter() {
        use Node::*;

        use super::NodeIndex::*;

        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000"));
        tree.filter(&InstructionFilter::parse("00000001"));
        assert_eq!(
            tree,
            FilterTree {
                entries: vec![
                    Branch {
                        is_0: Index(U40::new(1)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(2)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(3)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(4)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(5)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Index(U40::new(6)),
                        is_1: Enumerate
                    },
                    Branch {
                        is_0: Skip,
                        is_1: Enumerate
                    },
                ],
                empty: Vec::new(),
            }
        );
    }

    #[test]
    pub fn print_tree() {
        let mut tree = FilterTree::new();
        tree.filter(&InstructionFilter::parse("00000000"));
        tree.filter(&InstructionFilter::parse("00000001"));
        tree.filter(&InstructionFilter::parse("1100____"));

        println!("{tree:?}");
    }

    #[test]
    pub fn big_tree() {
        let mut tree = FilterTree::new();
        //11000101 00000011 01011101 10_00100 00__0_1_ 0__00_00 0000__00 00000000 00000100
        tree.filter(&InstructionFilter::parse(
            "11000101 ____1_11 01011101 10___100 ____0_1_ 1_______ _1___00_ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 0___1_11 010111_1 10___100 ____0_1_ ___1____ 010____0 ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 __0_1111 010111_1 10_0_100 ____0_1_ 1____1__ _1001__1 ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 0_____11 010111_1 10__0100 ____0_1_ ___1____ _101___1 ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 _0___111 010111_1 10_0_100 ____0_1_ ________ __1_____ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 01011101 10_0_100 ____0_1_ ______1_ 1__0____ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 _00___11 01011101 10_0_100 ____0_1_ ____0_1_ 1___000_ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 _____111 010111_1 10___100 ____0_1_ ________ 1__1__1_ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 _____111 010111_1 100__100 ____0_1_ ________ 1____1__ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 __0___11 010111_1 10___100 ____0_1_ ________ ___1100_ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ___01_11 01011101 1000_100 ____0_1_ ________ ____0__0 ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ _______1 ________ ________ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 00__0_1_ _______0 00______ 00000000 00000000",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ________ ________ ________ _______1",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ________ ________ ________ ______10",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ___1____ ________ ________ _____1__",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ________ ________ ________ ____1___",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10__0100 ____0_1_ ________ ________ ________ ___1____",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ________ ________ ________ __1_____",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ________ ________ ________ _1______",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ________ ________ ________ 1_______",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 __0___11 010111_1 10___100 ____0_1_ ________ 000___01 _______1 ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 _0____11 01011101 10___100 ____0_1_ ________ _______1 ______1_ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ________ ________ _____1__ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ___0__11 01011101 10___100 ____0_1_ ________ ________ ____1___ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ________ ________ ___1____ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ ________ ________ __1_____ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 ______11 010111_1 10___100 ____0_1_ 1_______ ________ _1______ ________",
        ));
        tree.filter(&InstructionFilter::parse(
            "11000101 _0____11 010111_1 10___100 ____0_1_ ________ ________ 1_______ ________",
        ));

        println!("{tree:?}");
    }

    #[test]
    pub fn covers() {
        let f = InstructionFilter::parse("00001100 000__0__");
        let g = InstructionFilter::parse("00001100 0_0__0__");
        let filters = [
            InstructionFilter::parse("00001100 000__000"),
            InstructionFilter::parse("00001100 000__001"),
            InstructionFilter::parse("00001100 000__010"),
            InstructionFilter::parse("00001100 000__011"),
        ];

        let mut tree = FilterTree::new();
        for filter in filters {
            tree.filter(&filter);
        }

        assert!(tree.covers(&f));
        assert!(!tree.covers(&g));
    }
}
