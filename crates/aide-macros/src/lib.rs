use darling::{FromDeriveInput, FromField, FromVariant};
use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_error::proc_macro_error;
use quote::{quote, ToTokens};
use syn::{parse_macro_input, parse_quote, Attribute, AttrStyle, DeriveInput, Expr, Generics, Ident, Item, ItemMod, Lit, LitStr, MacroDelimiter, Meta, MetaList, Path, PathArguments, PathSegment, Token, Type};
use syn::punctuated::Punctuated;
use syn::token::{Bracket, Paren};

extern crate proc_macro;

#[derive(Default, FromDeriveInput)]
#[darling(default, attributes(aide))]
struct OperationIoOpts {
    input: bool,
    input_with: Option<Type>,
    output: bool,
    output_with: Option<Type>,
    json_schema: bool,
}

/// A helper to reduce boilerplate for implementing [`OperationInput`]
/// and [`OperationOutput`] for common use-cases.
///
/// # Examples
///
/// The following implements an empty [`OperationInput`] and
/// [`OperationOutput`] so that the type can be used in documented
/// handlers but does not modify the documentation generation in any way.
///
/// ```ignore
/// use aide::{OperationInput, OperationOutput};
/// # use aide_macros::{OperationInput, OperationOutput};
///
/// #[derive(OperationIo)]
/// struct MyExtractor;
/// ```
///
/// By default both [`OperationInput`] and [`OperationOutput`] are implemented.
/// It is possible to restrict either with the `input` and `output` parameters.
///
/// The following will only implement [`OperationOutput`]:
///
/// ```ignore
/// #[derive(OperationIo)]
/// #[aide(output)]
/// struct MyExtractor;
/// ```
///
/// We can use the implementations of another type,
/// this is useful for wrapping other (e.g. `Json`) extractors
/// that might alter runtime behaviour but the documentation remains the same.
///
/// Additionally passing the `json_schema` flag will put a
/// [`JsonSchema`] bound to all generic parameters.
///
/// ```ignore
/// #[derive(OperationIo)]
/// #[aide(
///     input_with = "some_other::Json<T>",
///     output_with = "some_other::Json<T>",
///     json_schema
/// )]
/// struct Json<T>(pub T);
/// ```
///
/// [`JsonSchema`]: https://docs.rs/schemars/latest/schemars/trait.JsonSchema.html
/// [`OperationInput`]: https://docs.rs/aide/latest/aide/operation/trait.OperationInput.html
/// [`OperationOutput`]: https://docs.rs/aide/latest/aide/operation/trait.OperationOutput.html
#[proc_macro_derive(OperationIo, attributes(aide))]
pub fn derive_operation_io(ts: TokenStream) -> TokenStream {
    let mut derive_input = parse_macro_input!(ts as DeriveInput);

    let OperationIoOpts {
        input_with,
        output_with,
        input,
        output,
        json_schema,
    } = OperationIoOpts::from_derive_input(&derive_input).unwrap();

    let name = &derive_input.ident;

    let generic_params = derive_input
        .generics
        .params
        .iter()
        .filter_map(|p| match p {
            syn::GenericParam::Type(t) => Some(t.ident.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();

    if json_schema {
        let wh = derive_input.generics.make_where_clause();

        for param in generic_params {
            wh.predicates
                .push(parse_quote!(#param: schemars::JsonSchema));
        }
    }

    let (i_gen, t_gen, w_gen) = derive_input.generics.split_for_impl();

    let mut ts = quote!();

    if !input && !output && input_with.is_none() && output_with.is_none() {
        ts.extend(quote! {
            impl #i_gen aide::OperationInput for #name #t_gen #w_gen {}
            impl #i_gen aide::OperationOutput for #name #t_gen #w_gen {
                type Inner = Self;
            }
        });
    } else {
        if input {
            ts.extend(quote! {
                impl #i_gen aide::OperationInput for #name #t_gen #w_gen {}
            });
        }
        if output {
            ts.extend(quote! {
                impl #i_gen aide::OperationOutput for #name #t_gen #w_gen {
                    type Inner = Self;
                }
            });
        }

        if let Some(input) = input_with {
            ts.extend(quote! {
                impl #i_gen aide::OperationInput for #name #t_gen #w_gen {
                    fn operation_input(
                        ctx: &mut aide::gen::GenContext,
                        operation: &mut aide::openapi::Operation
                    ) {
                        <#input as aide::OperationInput>::operation_input(
                            ctx,
                            operation
                        );
                    }
                }
            });
        }

        if let Some(output) = output_with {
            ts.extend(quote! {
                impl #i_gen aide::OperationOutput for #name #t_gen #w_gen {
                    type Inner = <#output as aide::OperationOutput>::Inner;
                    fn operation_response(
                        ctx: &mut aide::gen::GenContext,
                        operation: &mut aide::openapi::Operation
                    ) -> Option<aide::openapi::Response> {
                        <#output as aide::OperationOutput>::operation_response(
                            ctx,
                            operation
                        )
                    }
                    fn inferred_responses(
                        ctx: &mut aide::gen::GenContext,
                        operation: &mut aide::openapi::Operation
                    ) -> Vec<(Option<u16>, aide::openapi::Response)> {
                        <#output as aide::OperationOutput>::inferred_responses(
                            ctx,
                            operation
                        )
                    }
                }
            });
        }
    }

    ts.into()
}

#[derive(FromDeriveInput)]
#[darling(attributes(response), forward_attrs(doc))]
struct IntoResponseOpts {
    ident: Ident,
    generics: Generics,
    data: darling::ast::Data<IntoResponseVariant, ResponseField>,
    attrs: Vec<Attribute>,
    status: Option<String>,
    body: Option<Type>,
    content_type: Option<LitStr>,
}

#[derive(FromVariant)]
#[darling(attributes(response), forward_attrs(doc))]
struct IntoResponseVariant {
    ident: Ident,
    fields: darling::ast::Fields<ResponseField>,
    attrs: Vec<Attribute>,
    status: String,
    body: Option<Type>,
    content_type: Option<LitStr>,
}

#[derive(FromField)]
#[darling(attributes())]
struct ResponseField {
    ident: Option<Ident>,
    ty: Type,
}

#[proc_macro_error]
#[proc_macro_derive(IntoResponse, attributes(transform, response))]
pub fn into_response(input: TokenStream) -> TokenStream {
    let derive_input = syn::parse_macro_input!(input);
    let into_response = IntoResponseOpts::from_derive_input(&derive_input).unwrap();

    into_response.to_token_stream().into()
}

#[derive(FromDeriveInput)]
#[darling(attributes(transform))]
struct TransformOpts {
    summary: Option<String>,
}

#[proc_macro_error]
#[proc_macro_derive(OperationOutput, attributes(response))]
pub fn operation_output(input: TokenStream) -> TokenStream {
    let derive_input = syn::parse_macro_input!(input);
    let operation_output = IntoResponseOpts::from_derive_input(&derive_input).unwrap();
    let transform_opts = TransformOpts::from_derive_input(&derive_input).unwrap();

    OperationOutputBuilder(operation_output, transform_opts).to_token_stream().into()
}

#[proc_macro_error]
#[proc_macro_attribute]
pub fn api(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = args.into();
    let mut module = parse_macro_input!(input as ItemMod);
    let Some((_, items)) = &mut module.content else {
        return module.to_token_stream().into();
    };
    for i in 0..items.len() {
        match &mut items[i] {
            Item::Struct(s) => add_transform(&mut s.attrs, &args),
            Item::Enum(e) => add_transform(&mut e.attrs, &args),
            _ => {}
        }
    }
    module.to_token_stream().into()
}

impl ToTokens for IntoResponseOpts {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let responder_arms = match &self.data {
            darling::ast::Data::Struct(fields) => vec![
                IntoResponseArmBuilder {
                    outer_ident: None,
                    ident: &self.ident,
                    fields: fields,
                    attrs: &self.attrs,
                    status: self.status.as_deref().unwrap_or("OK"),
                    body: self.body.as_ref(),
                    content_type: self.content_type.as_ref(),
                }.build()
            ],
            darling::ast::Data::Enum(enum_value) => enum_value
                .iter()
                .map(|variant| IntoResponseArmBuilder {
                    outer_ident: Some(&self.ident),
                    ident: &variant.ident,
                    fields: &variant.fields,
                    attrs: &variant.attrs,
                    status: &variant.status,
                    body: variant.body.as_ref().or(self.body.as_ref()),
                    content_type: variant.content_type.as_ref(),
                }.build())
                .collect::<Vec<proc_macro2::TokenStream>>(),
        };

        let ident = &self.ident;
        let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();

        tokens.extend(quote!{
            impl #impl_generics axum::response::IntoResponse for #ident #ty_generics #where_clause {
                fn into_response(self) -> axum::response::Response {
                    match self {
                        #(#responder_arms),*
                    }
                }
            }
        })
    }
}

struct IntoResponseArmBuilder<'a> {
    outer_ident: Option<&'a Ident>,
    ident: &'a Ident,
    fields: &'a darling::ast::Fields<ResponseField>,
    attrs: &'a[Attribute],
    status: &'a str,
    body: Option<&'a Type>,
    content_type: Option<&'a LitStr>,
}

impl<'a> IntoResponseArmBuilder<'a> {
    fn build(self) -> proc_macro2::TokenStream {
        let outer_ident = self.outer_ident.map(|ident| quote!(#ident::));
        let ident = self.ident;
        let ty = self.body;
        let response_attr = self.get_response_attr();

        if ty.is_none() {
            return quote!(#outer_ident #ident { .. } => self.attr_into_response(#response_attr));
        }

        match self.fields.style {
            darling::ast::Style::Struct => {
                let idents = self.fields.fields.iter().map(|field| &field.ident).collect::<Vec<_>>();
                quote!(
                    #outer_ident #ident { #(#idents),* } => #ty::from((#(#idents),*))
                        .attr_into_response(#response_attr)
                )
            },
            darling::ast::Style::Tuple => {
                let idents = self.fields.fields.iter().enumerate().map(|(i, _)| {
                    let mut ident = i.to_string();
                    ident.insert(0, 'i');
                    return Ident::new(&ident, Span::call_site());
                }).collect::<Vec<_>>();
                quote!(
                    #outer_ident #ident(#(#idents),*) => #ty::from((#(#idents),*))
                        .attr_into_response(#response_attr)
                )
            },
            darling::ast::Style::Unit => quote!(
                #outer_ident #ident => #ty::default().attr_into_response(#response_attr)
            ),
        }
    }

    fn get_response_attr(&self) -> proc_macro2::TokenStream {
        let status = Ident::new(&self.status, Span::call_site());
        let description = self.attrs.iter().filter_map(|attr| {
            attr.path().get_ident().filter(|&ident| ident == "doc")?;
            let Meta::NameValue(name_value) = &attr.meta else { return None };
            let Expr::Lit(doc_comment) = &name_value.value else { return None };
            let Lit::Str(comment) = &doc_comment.lit else { return None };
            Some(comment.value().trim().to_string())
        }).collect::<Vec<String>>().join("\n");
        let default_content_type = LitStr::new("application/json", Span::call_site());
        let content_type = self.content_type.unwrap_or(&default_content_type);

        return quote!(aide::axum::ResponseAttributes{
            status_code: axum::http::StatusCode::#status,
            content_type: #content_type,
            description: #description,
        });
    }
}

struct OperationOutputBuilder(IntoResponseOpts, TransformOpts);

impl ToTokens for OperationOutputBuilder {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let OperationOutputBuilder(response_opts, TransformOpts { summary }) = self;
        let summary = summary.as_ref().map(|summ| quote!(operation.summary = Some(#summ.into());));
        let inferred_responses = match &response_opts.data {
            darling::ast::Data::Struct(fields) => vec![
                InferredResponsesBuilder {
                    ident: &response_opts.ident,
                    fields: fields,
                    attrs: &response_opts.attrs,
                    status: response_opts.status.as_deref().unwrap_or("OK"),
                    body: response_opts.body.as_ref(),
                    content_type: response_opts.content_type.as_ref(),
                }.build()
            ],
            darling::ast::Data::Enum(enum_value) => enum_value
                .iter()
                .map(|variant| InferredResponsesBuilder {
                    ident: &response_opts.ident,
                    fields: &variant.fields,
                    attrs: &variant.attrs,
                    status: &variant.status,
                    body: variant.body.as_ref().or(response_opts.body.as_ref()),
                    content_type: variant.content_type.as_ref(),
                }.build())
                .collect::<Vec<proc_macro2::TokenStream>>(),
        };

        let ident = &response_opts.ident;
        let (impl_generics, ty_generics, where_clause) = response_opts.generics.split_for_impl();

        tokens.extend(quote!{
            impl #impl_generics aide::operation::OperationOutput for #ident #ty_generics #where_clause {
                type Inner = Self;

                fn inferred_responses(
                    ctx: &mut aide::gen::GenContext,
                    operation: &mut aide::openapi::Operation,
                ) -> Vec<(Option<u16>, aide::openapi::Response)> {
                    #summary
                    [#(#inferred_responses),*].into()
                }
            }
        })
    }
}

struct InferredResponsesBuilder<'a> {
    ident: &'a Ident,
    fields: &'a darling::ast::Fields<ResponseField>,
    attrs: &'a[Attribute],
    status: &'a str,
    body: Option<&'a Type>,
    content_type: Option<&'a LitStr>,
}

impl<'a> InferredResponsesBuilder<'a> {
    fn build(self) -> proc_macro2::TokenStream {
        if self.body.is_none() {
            let ident = self.ident;
            return self.build_from_type(quote!(#ident));
        }

        let ty = self.body;
        match self.fields.style {
            darling::ast::Style::Struct | darling::ast::Style::Tuple => {
                let types = self.fields.fields.iter().map(|field| &field.ty);
                self.build_from_type(quote!(#ty<#(#types),*>))
            },
            darling::ast::Style::Unit => self.build_from_type(quote!(#ty)),
        }
    }

    fn build_from_type(&self, ty: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
        let status = status_code(self.status);
        let description = self.attrs.iter().filter_map(|attr| {
            attr.path().get_ident().filter(|&ident| ident == "doc")?;
            let Meta::NameValue(name_value) = &attr.meta else { return None };
            let Expr::Lit(doc_comment) = &name_value.value else { return None };
            let Lit::Str(comment) = &doc_comment.lit else { return None };
            Some(comment.value().trim().to_string())
        }).collect::<Vec<String>>().join("\n");
        let default_content_type = LitStr::new("application/json", Span::call_site());
        let content_type = self.content_type.unwrap_or(&default_content_type);

        quote!((Some(#status), aide::openapi::Response {
            description: #description.into(),
            content: aide::indexmap::IndexMap::from_iter([(
                #content_type.into(),
                aide::openapi::MediaType {
                    schema: Some(aide::openapi::SchemaObject {
                        json_schema: ctx.schema.subschema_for::<#ty>().into_object().into(),
                        example: None,
                        external_docs: None,
                    }),
                    ..Default::default()
                },
            )]),
            ..Default::default()
        }))
    }
}

fn add_transform(attrs: &mut Vec<Attribute>, transform_args: &proc_macro2::TokenStream) {
    if attrs.iter().find(|attr| attr.meta.path().is_ident("derive") && attr
        .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
        .unwrap()
        .iter()
        .find(|nested_meta| nested_meta.path().is_ident("OperationOutput"))
        .is_some()
    ).is_some() {
        attrs.push(Attribute {
            pound_token: Token![#](Span::call_site()),
            style: AttrStyle::Outer,
            bracket_token: Bracket(Span::call_site()),
            meta: Meta::List(MetaList {
                path: Path {
                    leading_colon: None,
                    segments: Punctuated::from_iter([
                        PathSegment {
                            ident: Ident::new("transform", Span::call_site()),
                            arguments: PathArguments::None,
                        }
                    ].into_iter()),
                },
                tokens: transform_args.clone(),
                delimiter: MacroDelimiter::Paren(Paren(Span::call_site())),
            })
        });
    }
}

fn status_code(status_name: &str) -> u16 {
    match status_name {
        "CONTINUE" => 100,
        "SWITCHING_PROTOCOLS" => 101,
        "PROCESSING" => 102,
        "OK" => 200,
        "CREATED" => 201,
        "ACCEPTED" => 202,
        "NON_AUTHORITATIVE_INFORMATION" => 203,
        "NO_CONTENT" => 204,
        "RESET_CONTENT" => 205,
        "PARTIAL_CONTENT" => 206,
        "MULTI_STATUS" => 207,
        "ALREADY_REPORTED" => 208,
        "IM_USED" => 226,
        "MULTIPLE_CHOICES" => 300,
        "MOVED_PERMANENTLY" => 301,
        "FOUND" => 302,
        "SEE_OTHER" => 303,
        "NOT_MODIFIED" => 304,
        "USE_PROXY" => 305,
        "TEMPORARY_REDIRECT" => 307,
        "PERMANENT_REDIRECT" => 308,
        "BAD_REQUEST" => 400,
        "UNAUTHORIZED" => 401,
        "PAYMENT_REQUIRED" => 402,
        "FORBIDDEN" => 403,
        "NOT_FOUND" => 404,
        "METHOD_NOT_ALLOWED" => 405,
        "NOT_ACCEPTABLE" => 406,
        "PROXY_AUTHENTICATION_REQUIRED" => 407,
        "REQUEST_TIMEOUT" => 408,
        "CONFLICT" => 409,
        "GONE" => 410,
        "LENGTH_REQUIRED" => 411,
        "PRECONDITION_FAILED" => 412,
        "PAYLOAD_TOO_LARGE" => 413,
        "URI_TOO_LONG" => 414,
        "UNSUPPORTED_MEDIA_TYPE" => 415,
        "RANGE_NOT_SATISFIABLE" => 416,
        "EXPECTATION_FAILED" => 417,
        "IM_A_TEAPOT" => 418,
        "MISDIRECTED_REQUEST" => 421,
        "UNPROCESSABLE_ENTITY" => 422,
        "LOCKED" => 423,
        "FAILED_DEPENDENCY" => 424,
        "UPGRADE_REQUIRED" => 426,
        "PRECONDITION_REQUIRED" => 428,
        "TOO_MANY_REQUESTS" => 429,
        "REQUEST_HEADER_FIELDS_TOO_LARGE" => 431,
        "UNAVAILABLE_FOR_LEGAL_REASONS" => 451,
        "INTERNAL_SERVER_ERROR" => 500,
        "NOT_IMPLEMENTED" => 501,
        "BAD_GATEWAY" => 502,
        "SERVICE_UNAVAILABLE" => 503,
        "GATEWAY_TIMEOUT" => 504,
        "HTTP_VERSION_NOT_SUPPORTED" => 505,
        "VARIANT_ALSO_NEGOTIATES" => 506,
        "INSUFFICIENT_STORAGE" => 507,
        "LOOP_DETECTED" => 508,
        "NOT_EXTENDED" => 510,
        "NETWORK_AUTHENTICATION_REQUIRED" => 511,
        _ => 0,
    }
}
