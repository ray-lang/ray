use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::LitStr;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::token::Comma;
use syn::{
    Expr, ExprLit, FnArg, Ident, ItemFn, ItemStruct, Lit, Meta, MetaNameValue, Pat, PatIdent,
    ReturnType, Type, parse_macro_input, spanned::Spanned,
};

#[proc_macro_attribute]
pub fn query(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let f = parse_macro_input!(item as ItemFn);

    // Only free functions for now.
    let vis = &f.vis;
    let sig = &f.sig;
    let fn_name = &sig.ident;
    let fn_name_str = fn_name.to_string();

    // Extract the return type.
    let ret_ty: Type = match &sig.output {
        ReturnType::Default => {
            return syn::Error::new(sig.span(), "#[query] functions must return a value")
                .to_compile_error()
                .into();
        }
        ReturnType::Type(_, ty) => *ty.clone(),
    };

    // Collect inputs. We expect first arg is db: &mut dyn Database (or &mut impl Database).
    let mut inputs_iter = sig.inputs.iter();

    let db_arg = match inputs_iter.next() {
        Some(FnArg::Typed(pat_ty)) => pat_ty,
        _ => {
            return syn::Error::new(sig.span(), "#[query] requires an explicit db argument")
                .to_compile_error()
                .into();
        }
    };

    // Grab the db identifier so we can use it in generated code.
    let db_ident: Ident = match db_arg.pat.as_ref() {
        Pat::Ident(PatIdent { ident, .. }) => ident.clone(),
        _ => {
            return syn::Error::new(
                db_arg.pat.span(),
                "#[query] db argument must be an identifier, like `db: &mut dyn Database`",
            )
            .to_compile_error()
            .into();
        }
    };

    // Remaining arguments become the key.
    // We support patterns that are simple identifiers only.
    let mut key_field_idents: Vec<Ident> = Vec::new();
    let mut key_field_types: Vec<Type> = Vec::new();
    let mut wrapper_args: Vec<proc_macro2::TokenStream> = Vec::new();
    let mut wrapper_params: Vec<proc_macro2::TokenStream> = Vec::new();
    let mut key_ctor_args: Vec<proc_macro2::TokenStream> = Vec::new();

    for arg in inputs_iter {
        let FnArg::Typed(pat_ty) = arg else {
            return syn::Error::new(arg.span(), "#[query] does not support receiver args")
                .to_compile_error()
                .into();
        };

        let ident = match pat_ty.pat.as_ref() {
            Pat::Ident(PatIdent { ident, .. }) => ident.clone(),
            _ => {
                return syn::Error::new(
                    pat_ty.pat.span(),
                    "#[query] only supports identifier parameters (no destructuring patterns)",
                )
                .to_compile_error()
                .into();
            }
        };

        let ty = (*pat_ty.ty).clone();

        // Wrapper should accept the same parameter style as the original.
        // If the original is `&T`, we keep `&T` and clone into the key.
        // If it is `T`, we pass it by value into the key.
        wrapper_params.push(quote! { #ident: #ty });
        wrapper_args.push(quote! { #ident });

        key_field_idents.push(ident.clone());

        // Key constructor, cloning when appropriate.
        if let Type::Reference(ref_ty) = ty {
            key_field_types.push(ref_ty.elem.as_ref().clone());
            key_ctor_args.push(quote! {
                #ident.clone()
            });
        } else {
            key_field_types.push(ty.clone());
            key_ctor_args.push(quote! {
                #ident
            });
        }
    }

    // Generated identifiers (UpperCamelCase).
    let mut parts: Vec<String> = fn_name_str
        .split('_')
        .filter(|s| !s.is_empty())
        .map(|s| {
            let mut chars = s.chars();
            match chars.next() {
                Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect();
    if parts.is_empty() {
        parts.push("Query".to_string());
    }
    let camel = parts.join("");
    let key_ident = format_ident!("Key{}", camel);
    let query_ident = format_ident!("Query{}", camel);

    // Rebuild the original function as an inner compute function.
    // We will keep the body unchanged, but it will take (db, key) where key destructures fields.
    let body = &f.block;

    let key_destructure = if key_field_idents.is_empty() {
        quote! {}
    } else {
        quote! {
            let #key_ident { #(#key_field_idents),* } = key;
        }
    };

    // The wrapper function keeps the original name/signature (except it is always `pub` as original).
    // It constructs the key and calls db.query::<GeneratedQuery>(key).
    let db_ty = db_arg.ty.as_ref();
    let wrapper_fn = quote! {
        #vis fn #fn_name(#db_ident: #db_ty #(, #wrapper_params)*) -> #ret_ty {
            let key = #key_ident { #(#key_field_idents: #key_ctor_args),* };
            #db_ident.query::<#query_ident>(key)
        }
    };

    // The compute implementation uses the user body.
    // It destructures the key into local variables, then runs the user block.
    let query_impl = quote! {
        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        struct #key_ident {
            #(#key_field_idents: #key_field_types),*
        }

        struct #query_ident;

        impl Query for #query_ident {
            type Key = #key_ident;
            type Value = #ret_ty;

            const NAME: &'static str = #fn_name_str;

            fn compute(#db_ident: #db_ty, key: Self::Key) -> Self::Value {
                #key_destructure
                #body
            }
        }
    };

    // Put it all together.
    let expanded = quote! {
        #query_impl
        #wrapper_fn
    };

    expanded.into()
}

#[proc_macro_attribute]
pub fn input(attr: TokenStream, item: TokenStream) -> TokenStream {
    let item_clone = item.clone();
    if let Ok(s) = syn::parse::<ItemStruct>(item_clone) {
        return input_struct(attr, s);
    }

    let f = parse_macro_input!(item as ItemFn);
    let vis = &f.vis;
    let sig = &f.sig;
    let fn_name = &sig.ident;
    let fn_name_str = fn_name.to_string();

    let ret_ty: Type = match &sig.output {
        ReturnType::Default => {
            return syn::Error::new(sig.span(), "#[input] functions must return a value")
                .to_compile_error()
                .into();
        }
        ReturnType::Type(_, ty) => *ty.clone(),
    };

    let mut inputs_iter = sig.inputs.iter();
    let db_arg = match inputs_iter.next() {
        Some(FnArg::Typed(pat_ty)) => pat_ty,
        _ => {
            return syn::Error::new(sig.span(), "#[input] requires an explicit db argument")
                .to_compile_error()
                .into();
        }
    };

    let db_ident: Ident = match db_arg.pat.as_ref() {
        Pat::Ident(PatIdent { ident, .. }) => ident.clone(),
        _ => {
            return syn::Error::new(
                db_arg.pat.span(),
                "#[input] db argument must be an identifier",
            )
            .to_compile_error()
            .into();
        }
    };

    let key_arg = match inputs_iter.next() {
        Some(FnArg::Typed(pat_ty)) => pat_ty,
        _ => {
            return syn::Error::new(sig.span(), "#[input] requires a key argument")
                .to_compile_error()
                .into();
        }
    };

    if inputs_iter.next().is_some() {
        return syn::Error::new(sig.span(), "#[input] takes exactly two arguments")
            .to_compile_error()
            .into();
    }

    let key_ident: Ident = match key_arg.pat.as_ref() {
        Pat::Ident(PatIdent { ident, .. }) => ident.clone(),
        _ => {
            return syn::Error::new(
                key_arg.pat.span(),
                "#[input] only supports identifier parameters",
            )
            .to_compile_error()
            .into();
        }
    };

    let key_ty = (*key_arg.ty).clone();
    let key_field_ty = match &key_ty {
        Type::Reference(reference) => (*reference.elem).clone(),
        _ => key_ty.clone(),
    };

    let key_ctor = if matches!(key_ty, Type::Reference(_)) {
        quote! { #key_ident.clone() }
    } else {
        quote! { #key_ident }
    };

    let (key_override, fingerprint_path) = match parse_input_args(attr, sig.span(), false) {
        Ok(result) => result,
        Err(err) => return err.to_compile_error().into(),
    };
    if key_override.is_some() {
        return syn::Error::new(sig.span(), "#[input] on functions does not accept key=")
            .to_compile_error()
            .into();
    }

    let input_ident = format_ident!("Input{}", fn_name_str);
    let db_ty = db_arg.ty.as_ref();
    let getter_fn = quote! {
        #vis fn #fn_name(#db_ident: #db_ty, #key_ident: #key_ty) -> #ret_ty {
            #db_ident.get_input::<#input_ident>(#key_ctor)
        }
    };

    let setter_ident = format_ident!("set_{}", fn_name);
    let setter_fn = quote! {
        #vis fn #setter_ident(#db_ident: #db_ty, #key_ident: #key_ty, value: #ret_ty) {
            #db_ident.set_input::<#input_ident>(#key_ctor, value)
        }
    };

    let input_impl = quote! {
        impl #input_ident {
            #vis fn new(#db_ident: #db_ty, #key_ident: #key_ty, value: #ret_ty) {
                #setter_ident(#db_ident, #key_ident, value);
            }
        }
    };

    let fingerprint_impl = if let Some(path) = fingerprint_path {
        quote! {
            fn fingerprint(value: &Self::Value) -> u64 {
                #path(value)
            }
        }
    } else {
        quote! {
            fn fingerprint(value: &Self::Value) -> u64 {
                let mut hasher = fnv::FnvHasher::default();
                value.hash(&mut hasher);
                hasher.finish()
            }
        }
    };

    let expanded = quote! {
        struct #input_ident;

        impl Input for #input_ident {
            type Key = #key_field_ty;
            type Value = #ret_ty;

            const NAME: &'static str = #fn_name_str;

            #fingerprint_impl
        }

        #getter_fn
        #setter_fn
        #input_impl
    };

    expanded.into()
}

fn input_struct(attr: TokenStream, s: ItemStruct) -> TokenStream {
    let vis = &s.vis;
    let ident = &s.ident;
    let name_str = ident.to_string();
    let fields = &s.fields;

    if fields.is_empty() {
        return syn::Error::new(s.span(), "#[input] struct must have at least one field")
            .to_compile_error()
            .into();
    }

    // Collect field information
    let mut field_names: Vec<Ident> = Vec::new();
    let mut field_types: Vec<Type> = Vec::new();
    let is_tuple_struct = fields
        .iter()
        .next()
        .map(|f| f.ident.is_none())
        .unwrap_or(false);

    for (i, field) in fields.iter().enumerate() {
        let name = field
            .ident
            .clone()
            .unwrap_or_else(|| format_ident!("field_{}", i));
        field_names.push(name);
        field_types.push(field.ty.clone());
    }

    // Constructor expression for `new` method
    let ctor_expr = if is_tuple_struct {
        quote! { #ident(#(#field_names),*) }
    } else {
        quote! { #ident { #(#field_names),* } }
    };

    // Parameters for `new` method
    let new_params: Vec<_> = field_names
        .iter()
        .zip(field_types.iter())
        .map(|(name, ty)| quote! { #name: #ty })
        .collect();

    let (key_ty, fingerprint_path) = match parse_input_args(attr, s.span(), true) {
        Ok(result) => result,
        Err(err) => return err.to_compile_error().into(),
    };

    let has_key_override = key_ty.is_some();
    let key_ty = key_ty.unwrap_or_else(|| syn::parse_quote!(#ident));

    let fingerprint_impl = if let Some(path) = fingerprint_path {
        quote! {
            fn fingerprint(value: &Self::Value) -> u64 {
                #path(value)
            }
        }
    } else {
        quote! {
            fn fingerprint(value: &Self::Value) -> u64 {
                let mut hasher = fnv::FnvHasher::default();
                value.hash(&mut hasher);
                hasher.finish()
            }
        }
    };

    // For self-keyed inputs (no key override), generate value/set_value accessors
    let accessors = if has_key_override {
        quote! {}
    } else {
        quote! {
            impl #ident {
                #vis fn value(&self, db: &Database) -> #ident {
                    db.get_input::<#ident>(self.clone())
                }

                #vis fn set_value(&self, db: &Database, value: #ident) {
                    db.set_input::<#ident>(self.clone(), value);
                }
            }
        }
    };

    let expanded = quote! {
        #s

        impl Input for #ident {
            type Key = #key_ty;
            type Value = #ident;

            const NAME: &'static str = #name_str;

            #fingerprint_impl
        }

        impl #ident {
            #vis fn new(db: &Database, key: #key_ty, #(#new_params),*) {
                db.set_input::<#ident>(key, #ctor_expr);
            }
        }

        #accessors
    };

    expanded.into()
}

fn parse_input_args(
    attr: TokenStream,
    span: proc_macro2::Span,
    allow_key: bool,
) -> Result<(Option<Type>, Option<syn::Path>), syn::Error> {
    let mut key_ty: Option<Type> = None;
    let mut fingerprint_path: Option<syn::Path> = None;

    if attr.is_empty() {
        return Ok((key_ty, fingerprint_path));
    }

    let metas = Punctuated::<Meta, Comma>::parse_terminated
        .parse2(attr.into())
        .map_err(|_| syn::Error::new(span, "invalid #[input] attribute syntax"))?;
    for meta in metas {
        let Meta::NameValue(MetaNameValue { path, value, .. }) = meta else {
            return Err(syn::Error::new(span, "invalid #[input] attribute syntax"));
        };

        if path.is_ident("fingerprint") {
            fingerprint_path = Some(parse_string_lit(value, "fingerprint")?);
            continue;
        }

        if path.is_ident("key") {
            if !allow_key {
                return Err(syn::Error::new(
                    path.span(),
                    "#[input] on functions does not accept key=",
                ));
            }

            key_ty = Some(parse_string_lit(value, "key")?);
            continue;
        }

        return Err(syn::Error::new(path.span(), "unknown #[input] argument"));
    }

    Ok((key_ty, fingerprint_path))
}

fn parse_string_lit<T: syn::parse::Parse>(
    value: Expr,
    name: &'static str,
) -> Result<T, syn::Error> {
    let lit = get_string_lit(value, name)?;
    lit.parse::<T>()
}

fn get_string_lit(value: Expr, name: &'static str) -> Result<LitStr, syn::Error> {
    let Expr::Lit(ExprLit {
        lit: Lit::Str(lit), ..
    }) = value
    else {
        return Err(syn::Error::new(
            value.span(),
            format!("{} must be a string literal", name),
        ));
    };

    Ok(lit)
}
