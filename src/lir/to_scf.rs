use std::collections::HashMap;

use crate::{graph::TopologicalSort, sort::SortByIndexSlice};

use super::{Block, ControlMarker, Func, If, Inst, Program};

#[derive(Debug)]
pub struct ControlBlock {
    child: Option<Box<ControlBlock>>,
    blocks: Vec<usize>,
}

impl ControlBlock {
    fn new() -> Self {
        Self {
            blocks: vec![],
            child: None,
        }
    }
}

pub struct Stackify {
    control_blocks: Vec<ControlBlock>,
}

impl Stackify {
    pub fn new() -> Self {
        Self {
            control_blocks: vec![],
        }
    }

    pub fn stackify(&mut self, func: &Func) {
        log::debug!("stackify: {}", func);
        let mut curr_block = ControlBlock::new();
        self._stackify(&mut curr_block, 0, 0, func);
        // let mut blocks = vec![0];
        // let mut stack = vec![];
        // let mut curr_stack = vec![ControlBlock::new()];

        // let mut loop_depth = 0;
        // while let Some(label) = blocks.pop() {
        //     curr_stack.last_mut().unwrap().blocks.push(label);
        //     let block = &func.blocks[label];
        //     if matches!(block.marker(), Some(ControlMarker::Loop)) {
        //         loop_depth += 1;
        //     }

        //     if let Some(last) = block.last() {
        //         match last {
        //             Inst::If(If {
        //                 then_label,
        //                 else_label,
        //                 ..
        //             }) => {
        //                 // pushed in stack order
        //                 blocks.push(*else_label);
        //                 blocks.push(*then_label);

        //                 // push a new control block onto the current stack (this will be the if body)
        //                 curr_stack.push(ControlBlock::new());
        //             }
        //             Inst::Goto(next_label) => {
        //                 if curr_stack.last().unwrap().blocks.contains(next_label) {
        //                     // the next label must be a loop header
        //                     // and the current block is the end of the loop
        //                     let last_blocks = curr_stack.pop().unwrap();
        //                     stack.push(last_blocks);

        //                     // create a new block to handle the next
        //                     curr_stack.push(ControlBlock::new());
        //                     loop_depth -= 1;
        //                     continue;
        //                 }

        //                 blocks.push(*next_label);
        //             }
        //             Inst::Break(_) => todo!("stackify break"),
        //             Inst::Return(_) => continue,
        //             i => panic!("COMPILER BUG: {} is not a control instruction", i),
        //         }
        //     }
        // }

        // while let Some(block) = curr_stack.pop() {
        //     stack.push(block);
        // }

        // for b in stack.iter().rev() {
        //     log::debug!("block: {:?}", b);
        // }

        // let mut curr = vec![];
        // for block in func.blocks.iter() {
        //     let label = block.label();
        //     curr.push(value)
        //     if let Some(last) = block.last() {
        //         match last {
        //             Inst::If(If { then_label, else_label, .. }) => {

        //             }
        //             Inst::Goto(next_label) => {

        //             }
        //             Inst::Break(_) => todo!("stackify break"),
        //             i => panic!("COMPILER BUG: {} is not a control instruction", i)
        //         }
        //     }
        // }

        // Sort the blocks topologically
        // log::debug!("before sort: {}", func);
        // func.sort_topologically();
        // log::debug!("stackify: {}", func);

        // // Calculate dominators so we can use them to place markers
        // let dominators = func.calculate_strict_dominators();
        // log::debug!("strict dominators: {:?}", dominators);

        // // Place the BLOCK/LOOP/TRY markers to indicate the beginnings of scopes.
        // self.place_markers(func, &dominators);

        // // Convert block operands in terminators to relative depth immediates.
        // self.rewrite_depth_immediates(func);

        // // Fix up block/loop/try signatures at the end of the function to conform to
        // // WebAssembly's rules.
        // self.fix_ends_at_end_of_function(func);

        // // Add an end instruction at the end of the function body.
        // self.append_end_to_function(func);
    }

    fn _stackify(
        &self,
        curr_block: &mut ControlBlock,
        label: usize,
        mut loop_depth: usize,
        func: &Func,
    ) -> Option<usize> {
        let block = &func.blocks[label];
        if block.is_loop_header() {
            curr_block.blocks.push(label);
            loop_depth += 1;
        }

        if let Some(last) = block.last() {
            match last {
                &Inst::If(If {
                    then_label,
                    else_label,
                    ..
                }) => {
                    self._stackify(curr_block, then_label, loop_depth, func);
                }
                &Inst::Goto(next_label) => {}
                Inst::Break(_) => todo!("stackify break"),
                Inst::Return(_) => { /* do nothing */ }
                i => panic!("COMPILER BUG: {} is not a control instruction", i),
            }
        }

        None
    }
}

// pub enum ControlMarker {
//     Block,
//     Loop,
// }

// pub struct ControlBlock {
//     markers: HashMap<usize, ControlMarker>,
//     blocks: Vec<usize>,
// }

// pub trait ToStructuredControlFlow {
//     type Output;
//     fn to_scf(&self) -> Self::Output;
// }

// impl ToStructuredControlFlow for Program {
//     type Output = ();
//     fn to_scf(&self) {
//         for func in self.funcs.iter() {
//             let indices = func.to_scf();
//         }
//         todo!()
//     }
// }

// impl ToStructuredControlFlow for Func {
//     type Output = Vec<usize>;

//     fn to_scf(&self) -> Self::Output {
//         log::debug!("to scf: {}", self);

//         let mut cfg = self.cfg.clone();
//         let mut groups = vec![];
//         let mut marker: Option<ControlMarker> = None;
//         let mut last = None;
//         let mut curr = vec![];
//         loop {
//             let blocks = cfg.toposort();
//             if blocks.len() == 0 {
//                 if cfg.len() == 0 {
//                     break;
//                 }

//                 // there is a cycle: we must find it and break it
//                 if let Some(block) =
//                     last.and_then(|idx| -> Option<&Block> { self.body.get(idx + 1) })
//                 {
//                     // this is the start of a loop
//                     let label = block.label();
//                     if cfg.remove(&label).is_some() {
//                         // unless it has already been removed add it
//                         marker = Some(ControlMarker::Loop);
//                         curr.push(label);
//                         last = Some(label);
//                     }
//                     continue;
//                 }

//                 break;
//             }

//             curr.extend(blocks);
//             last = curr.last().copied();
//             log::debug!("blocks: {:?}", curr);
//             groups.push((marker, curr));
//             curr = vec![];
//             marker = None;
//         }

//         vec![]
//     }
// }
