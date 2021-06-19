use std::collections::HashMap;

use lir::{GetLocals, MapLocals};

use crate::lir;

use super::Optimize;

pub(super) struct MinimizeLocals();

impl Optimize for MinimizeLocals {
    fn level(&self) -> usize {
        0
    }

    fn optimize_func(&self, func: &mut lir::Func) {
        // first, calculate the lifetimes of each local
        let mut lifetime_map = HashMap::new();
        let mut i = 0usize;
        for block in func.blocks.iter() {
            for inst in block.iter() {
                let locals = inst.get_locals();
                for &local in locals {
                    lifetime_map
                        .entry(local)
                        .and_modify(|(_, end)| {
                            *end = i;
                        })
                        .or_insert_with(|| (i, i));
                }

                i += 1;
            }
        }

        // order the lifetimes by increasing start point
        let mut lifetimes = lifetime_map.into_iter().collect::<Vec<_>>();
        lifetimes.sort_by_key(|(_, (start, _))| *start);

        log::debug!("lifetimes: {:?}\n{}", lifetimes, func);

        // then, determine the maximum number of locals required
        let mut total_locals = 0;
        let mut active = vec![];
        let mut free_locals = (func.params.len()..func.locals.len()).rev().collect();

        let mut local_map = HashMap::new();
        for interval in lifetimes {
            let (loc, _) = interval;
            if loc < func.params.len() {
                // ignore parameters
                continue;
            }

            expire_intervals(&interval, &mut active, &mut free_locals);

            let (prev_local, (start, end)) = interval;
            let new_local = free_locals.pop().unwrap();

            // let prev_local = resolve_local(prev_local, &local_map);
            // let new_local = resolve_local(new_local, &local_map);
            if prev_local != new_local {
                local_map.insert(prev_local, new_local);
            }

            active.push((new_local, (start, end)));
            active.sort_by_key(|(_, (_, end))| *end);
            if active.len() > total_locals {
                total_locals = active.len();
            }
        }

        func.map_locals(&local_map);
        // remove all unncessary locals
        func.locals.drain(total_locals..);
        log::debug!("minimize locals: {}", func);
    }
}

fn expire_intervals(
    curr_interval: &(usize, (usize, usize)),
    intervals: &mut Vec<(usize, (usize, usize))>,
    free_locals: &mut Vec<usize>,
) {
    intervals.sort_by_key(|(_, (_, end))| *end);

    let (_, (start, _)) = curr_interval;
    while intervals.len() > 0 {
        let (_, (_, end)) = &intervals[0];
        if end >= start {
            return;
        }

        let (loc, _) = intervals.remove(0);
        free_locals.push(loc);
    }
}
