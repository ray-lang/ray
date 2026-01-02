use std::collections::HashMap;

use ray_shared::{pathlib::Path, ty::Ty};
use ray_typing::{BindingKind, BindingRecord, binding_groups::BindingId, types::TyScheme};

use crate::passes::binding::BindingPassOutput;

fn binding_kind_for_scheme(scheme: &TyScheme) -> BindingKind {
    match scheme.mono() {
        Ty::Func(_, _) => BindingKind::Function { params: Vec::new() },
        _ => BindingKind::Value,
    }
}

pub fn inject_extern_bindings(
    output: &mut BindingPassOutput,
    extern_schemes: &HashMap<Path, TyScheme>,
) {
    for (path, scheme) in extern_schemes {
        if output.value_bindings.contains_key(path) {
            continue;
        }

        let binding = BindingId(output.next_binding);
        output.next_binding += 1;
        output.bindings.add_binding(binding);
        output.value_bindings.insert(path.clone(), binding);

        let mut record = BindingRecord::new(binding_kind_for_scheme(scheme));
        record.path = Some(path.clone());
        record.scheme = Some(scheme.clone());
        record.is_extern = true;
        output.binding_records.insert(binding, record);
    }
}

#[cfg(test)]
mod tests {
    use ray_typing::binding_groups::BindingGraph;

    use super::*;

    #[test]
    fn injects_extern_bindings_from_next_binding() {
        let mut output = BindingPassOutput {
            bindings: BindingGraph::new(),
            binding_records: Default::default(),
            node_bindings: Default::default(),
            value_bindings: Default::default(),
            next_binding: 10,
        };

        // Pre-existing binding should not be overwritten.
        output
            .value_bindings
            .insert(Path::from("core::keep"), BindingId(3));

        let mut extern_schemes = HashMap::new();
        extern_schemes.insert(
            Path::from("core::print"),
            TyScheme::from_mono(Ty::Func(vec![], Box::new(Ty::unit()))),
        );
        extern_schemes.insert(
            Path::from("core::keep"),
            TyScheme::from_mono(Ty::Func(vec![], Box::new(Ty::unit()))),
        );

        inject_extern_bindings(&mut output, &extern_schemes);

        let print_binding = output
            .value_bindings
            .get(&Path::from("core::print"))
            .copied()
            .expect("should inject binding for core::print");
        assert_eq!(print_binding, BindingId(10));
        assert_eq!(output.next_binding, 11);

        let keep_binding = output
            .value_bindings
            .get(&Path::from("core::keep"))
            .copied()
            .expect("should keep existing binding");
        assert_eq!(keep_binding, BindingId(3));

        let record = output
            .binding_records
            .get(&print_binding)
            .expect("should record binding record");
        assert_eq!(record.path.as_ref(), Some(&Path::from("core::print")));
        assert!(record.scheme.is_some(), "extern stub should carry scheme");
        assert!(record.is_extern, "extern stub should be marked extern");
        assert!(
            record.parent.is_none(),
            "extern stub should not rely on parent sentinel"
        );
    }
}
