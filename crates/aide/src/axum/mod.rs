//! Open API code generation for [`axum`].
//!
//! The implementation closely mimics the api of [`axum`] with
//! extra care taken in order to allow seamless transitions.
//!
//! The notable types are [`ApiRouter`] and [`ApiMethodRouter`] that wrap
//! [`axum::Router`] and [`axum::routing::MethodRouter`] respectively.
//! Likewise, the top-level methods in [`axum::routing`] have their counterparts
//! in [`routing`].
//!
//! # Examples
//!
//! Take the following `axum` example:
//!
//! ```no_run
//! use axum::{response::IntoResponse, routing::post, Json, Router};
//! use serde::Deserialize;
//!
//! #[derive(Deserialize)]
//! struct User {
//!     name: String,
//! }
//!
//! async fn hello_user(Json(user): Json<User>) -> impl IntoResponse {
//!     format!("hello {}", user.name)
//! }
//!
//! #[tokio::main]
//! async fn main() {
//!     let app = Router::new().route("/hello", post(hello_user));
//!
//!     axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
//!         .serve(app.into_make_service())
//!         .await
//!         .unwrap();
//! }
//! ```
//!
//! We can apply the following changes to generate documentation for it:
//!
//! ```no_run
//! // Replace some of the `axum::` types with `aide::axum::` ones.
//! use aide::{
//!     axum::{
//!         routing::{get, post},
//!         ApiRouter,
//!     },
//!     openapi::{Info, OpenApi},
//! };
//! use axum::{response::IntoResponse, Extension, Json};
//! use schemars::JsonSchema;
//! use serde::Deserialize;
//!
//! // We'll need to derive `JsonSchema` for
//! // all types that appear in the api documentation.
//! #[derive(Deserialize, JsonSchema)]
//! struct User {
//!     name: String,
//! }
//!
//! async fn hello_user(Json(user): Json<User>) -> impl IntoResponse {
//!     format!("hello {}", user.name)
//! }
//!
//! // Note that this clones the document on each request.
//! // To be more efficient, we could wrap it into an Arc,
//! // or even store it as a serialized string.
//! async fn serve_api(Extension(api): Extension<OpenApi>) -> impl IntoResponse {
//!     Json(api)
//! }
//!
//! #[tokio::main]
//! async fn main() {
//!     let app = ApiRouter::new()
//!         // Change `route` to `api_route` for the route
//!         // we'd like to expose in the documentation.
//!         .api_route("/hello", post(hello_user))
//!         // We'll serve our generated document here.
//!         .route("/api.json", get(serve_api));
//!
//!     let mut api = OpenApi {
//!         info: Info {
//!             description: Some("an example API".to_string()),
//!             ..Info::default()
//!         },
//!         ..OpenApi::default()
//!     };
//!
//!     axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
//!         .serve(
//!             app
//!                 // Generate the documentation.
//!                 .finish_api(&mut api)
//!                 // Expose the documentation to the handlers.
//!                 .layer(Extension(api))
//!                 .into_make_service(),
//!         )
//!         .await
//!         .unwrap();
//! }
//! ```
//!
//! Only routes added via `api_route` are visible in the documentation,
//! this makes exposed routes explicit and less error-prone.
//!
//! ## Adding details.
//!
//! The above example includes routes and request parameters but
//! it's lacking response types and additional metadata such as descriptions,
//! as these are not possible to infer just via types.
//!
//! ### Responses
//!
//! Generally we can add information at the following levels:
//!
//! - Operation level (e.g. [`get_with`](crate::axum::routing::get_with))
//! - Route level ([`api_route_with`](crate::axum::ApiRouter::api_route_with))
//! - API-level ([`finish_api_with`](crate::axum::ApiRouter::finish_api_with))
//!
//! All of these are additive and the API-level information will not override
//! route or operation metadata unless explicitly stated.
//!
//! With this being said, we can specify the response status code
//! and the type for our `hello_user` operation:
//!
//! ```ignore
//! // ...
//! .api_route(
//!     "/hello",
//!     post_with(hello_user, |op| op.response::<200, String>()),
//! )
//! // ...
//! ```
//!
//! And on the API-level we define that in every unspecified
//! case, we return some kind of text:
//!
//! ```ignore
//! // ...
//! app.finish_api_with(&mut api, |api| api.default_response::<String>())
//! // ...
//! ```
//!
//! ### Other Metadata
//!
//! We can extend our `hello_user` operation with further metadata:
//!
//! ```ignore
//! // ...
//! .api_route(
//!     "/hello",
//!     post_with(hello_user, |o| {
//!         o.id("helloUser")
//!             .description("says hello to the given user")
//!             .response_with::<200, String, _>(|res| {
//!                 res.description("a simple message saying hello to the user")
//!                     .example(String::from("hello Tom"))
//!             })
//!     }),
//! )
//! // ...
//! ```
//!
//! # Composability
//!
//! Just like in `axum`, nesting and merging routers is possible,
//! and the documented routes will be updated as expected.
//!

use std::{convert::Infallible, future::Future, mem, pin::Pin, sync::Arc};

use crate::{
    gen::{self, in_context},
    openapi::{Components, OpenApi, PathItem, ReferenceOr, SchemaObject},
    util::merge_paths,
};
use axum::{
    body::{Body, HttpBody},
    extract::connect_info::IntoMakeServiceWithConnectInfo,
    handler::Handler,
    http::Request,
    response::IntoResponse,
    routing::{IntoMakeService, Route},
    Router,
};
use indexmap::IndexMap;
use tower_layer::Layer;
use tower_service::Service;

use crate::{
    transform::{TransformOpenApi, TransformPathItem},
    util::path_colon_params,
};

use self::routing::ApiMethodRouter;

mod inputs;
mod outputs;

pub mod routing;

/// A wrapper over [`axum::Router`] that adds
/// API documentation-specific features.
#[must_use]
#[derive(Debug, Clone)]
pub struct ApiRouter<S = (), B = Body> {
    paths: IndexMap<String, PathItem>,
    router: Router<S, B>,
}

#[allow(clippy::mismatching_type_param_order)]
impl<B> ApiRouter<(), B>
where
    B: HttpBody + Send + 'static,
{
    /// Create a new router with no state.
    ///
    /// See [`axum::Router::new`] for details.
    pub fn new() -> Self {
        Self::with_state(())
    }
}

#[allow(clippy::mismatching_type_param_order)]
impl<B> Default for ApiRouter<(), B>
where
    B: HttpBody + Send + 'static,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<S, B> ApiRouter<S, B>
where
    B: HttpBody + Send + 'static,
    S: Send + Sync + 'static,
{
    /// Create a new router with state.
    ///
    /// See [`axum::Router::with_state`] for details.
    pub fn with_state(state: S) -> Self {
        Self::with_state_arc(Arc::new(state))
    }

    /// Create a new router with state.
    ///
    /// See [`axum::Router::with_state_arc`] for details.
    pub fn with_state_arc(state: Arc<S>) -> Self {
        Self {
            paths: IndexMap::default(),
            router: Router::with_state_arc(state),
        }
    }

    /// Create a route to the given method router and include it in
    /// the API documentation.
    ///
    /// As opposed to [`route`](crate::axum::ApiRouter::route), this method only accepts an [`ApiMethodRouter`].
    ///
    /// See [`axum::Router::route`] for details.
    #[tracing::instrument(skip_all, fields(%path))]
    pub fn api_route(mut self, path: &str, mut method_router: ApiMethodRouter<S, B>) -> Self {
        in_context(|ctx| {
            let new_path_item = method_router.take_path_item();

            if let Some(path_item) = self.paths.get_mut(path) {
                merge_paths(ctx, path, path_item, new_path_item);
            } else {
                self.paths.insert(path.into(), new_path_item);
            }
        });

        self.router = self.router.route(path, method_router.router);
        self
    }

    /// Create a route to the given method router and include it in
    /// the API documentation.
    ///
    /// This method accepts a transform function to edit
    /// the generated API documentation with.
    ///
    /// See [`axum::Router::route`] or [`api_route`](crate::axum::ApiRouter::api_route) for details.
    #[tracing::instrument(skip_all, fields(%path))]
    pub fn api_route_with(
        mut self,
        path: &str,
        mut method_router: ApiMethodRouter<S, B>,
        transform: impl FnOnce(TransformPathItem) -> TransformPathItem,
    ) -> Self {
        let mut p = method_router.take_path_item();

        let t = transform(TransformPathItem::new(&mut p));

        if !t.hidden {
            self.paths.insert(path.into(), p);
        }

        self.router = self.router.route(path, method_router.router);
        self
    }

    /// Turn this router into an [`axum::Router`] while merging
    /// generated documentation into the provided [`OpenApi`].
    #[tracing::instrument(skip_all)]
    pub fn finish_api(mut self, api: &mut OpenApi) -> Router<S, B> {
        self.merge_api(api);
        self.router
    }

    /// Turn this router into an [`axum::Router`] while merging
    /// generated documentation into the provided [`OpenApi`].
    ///
    /// This method accepts a transform function to edit
    /// the generated API documentation with.
    #[tracing::instrument(skip_all)]
    pub fn finish_api_with<F>(mut self, api: &mut OpenApi, transform: F) -> Router<S, B>
    where
        F: FnOnce(TransformOpenApi) -> TransformOpenApi,
    {
        self.merge_api(api);
        let _ = transform(TransformOpenApi::new(api));
        self.router
    }

    fn merge_api(&mut self, api: &mut OpenApi) {
        if api.paths.is_none() {
            api.paths = Some(Default::default());
        }

        let paths = api.paths.as_mut().unwrap();

        paths.paths = mem::take(&mut self.paths)
            .into_iter()
            .map(|(route, path)| {
                (
                    path_colon_params(&route).into_owned(),
                    ReferenceOr::Item(path),
                )
            })
            .collect();

        let needs_reset =
            in_context(|ctx| {
                if !ctx.extract_schemas {
                    return false;
                }

                if api.components.is_none() {
                    api.components = Some(Components::default());
                }

                let components = api.components.as_mut().unwrap();

                components
                    .schemas
                    .extend(ctx.schema.take_definitions().into_iter().map(
                        |(name, json_schema)| {
                            (
                                name,
                                SchemaObject {
                                    json_schema,
                                    example: None,
                                    external_docs: None,
                                },
                            )
                        },
                    ));

                true
            });

        if needs_reset {
            gen::reset_context();
        }
    }
}

/// Existing methods extended with api-specifics.
impl<S, B> ApiRouter<S, B>
where
    B: HttpBody + Send + 'static,
    S: Send + Sync + 'static,
{
    /// See [`axum::Router::route`] for details.
    ///
    /// This method accepts [`ApiMethodRouter`] but does not generate API documentation.
    #[tracing::instrument(skip_all)]
    pub fn route(mut self, path: &str, method_router: impl Into<ApiMethodRouter<S, B>>) -> Self {
        self.router = self.router.route(path, method_router.into().router);
        self
    }

    /// See [`axum::Router::route_service`] for details.
    #[tracing::instrument(skip_all)]
    pub fn route_service<T>(mut self, path: &str, service: T) -> Self
    where
        T: Service<Request<B>, Error = Infallible> + Clone + Send + 'static,
        T::Response: IntoResponse,
        T::Future: Send + 'static,
    {
        self.router = self.router.route_service(path, service);
        self
    }

    /// See [`axum::Router::nest`] for details.
    ///
    /// If an another [`ApiRouter`] is provided, the generated documentations
    /// are nested as well.
    #[tracing::instrument(skip_all)]
    pub fn nest<T>(mut self, mut path: &str, svc: impl Into<ServiceOrApiRouter<S, B, T>>) -> Self
    where
        T: Service<Request<B>, Error = Infallible> + Clone + Send + 'static,
        T::Response: IntoResponse,
        T::Future: Send + 'static,
    {
        match svc.into() {
            ServiceOrApiRouter::Router(r) => {
                self.router = self.router.nest(path, r.router);

                path = path.trim_end_matches('/');

                self.paths.extend(
                    r.paths
                        .into_iter()
                        .map(|(route, path_item)| (path.to_string() + &route, path_item)),
                );
            }
            ServiceOrApiRouter::Service(svc) => {
                self.router = self.router.nest(path, svc);
            }
        }

        self
    }

    /// See [`axum::Router::merge`] for details.
    ///
    /// If an another [`ApiRouter`] is provided, the generated documentations
    /// are merged as well..
    #[tracing::instrument(skip_all)]
    pub fn merge<S2, R>(mut self, other: R) -> Self
    where
        R: Into<ApiRouter<S2, B>>,
        S2: Send + Sync + 'static,
    {
        let other: ApiRouter<S2, B> = other.into();

        self.paths.extend(other.paths);
        self.router = self.router.merge(other.router);
        self
    }

    /// See [`axum::Router::layer`] for details.
    #[tracing::instrument(skip_all)]
    pub fn layer<L, NewReqBody>(self, layer: L) -> ApiRouter<S, NewReqBody>
    where
        L: Layer<Route<B>>,
        L::Service: Service<Request<NewReqBody>> + Clone + Send + 'static,
        <L::Service as Service<Request<NewReqBody>>>::Response: IntoResponse + 'static,
        <L::Service as Service<Request<NewReqBody>>>::Error: Into<Infallible> + 'static,
        <L::Service as Service<Request<NewReqBody>>>::Future: Send + 'static,
    {
        ApiRouter {
            paths: self.paths,
            router: self.router.layer(layer),
        }
    }

    /// See [`axum::Router::route_layer`] for details.
    #[tracing::instrument(skip_all)]
    pub fn route_layer<L>(mut self, layer: L) -> Self
    where
        L: Layer<Route<B>>,
        L::Service: Service<Request<B>> + Clone + Send + 'static,
        <L::Service as Service<Request<B>>>::Response: IntoResponse + 'static,
        <L::Service as Service<Request<B>>>::Error: Into<Infallible> + 'static,
        <L::Service as Service<Request<B>>>::Future: Send + 'static,
    {
        self.router = self.router.route_layer(layer);
        self
    }

    /// See [`axum::Router::fallback`] for details.
    #[tracing::instrument(skip_all)]
    pub fn fallback<H, T>(mut self, handler: H) -> Self
    where
        H: Handler<T, S, B>,
        T: 'static,
    {
        self.router = self.router.fallback(handler);
        self
    }

    /// See [`axum::Router::fallback_service`] for details.
    #[tracing::instrument(skip_all)]
    pub fn fallback_service<T>(mut self, svc: T) -> Self
    where
        T: Service<Request<B>, Error = Infallible> + Clone + Send + 'static,
        T::Response: IntoResponse,
        T::Future: Send + 'static,
    {
        self.router = self.router.fallback_service(svc);
        self
    }

    /// See [`axum::Router::into_make_service`] for details.
    #[tracing::instrument(skip_all)]
    #[must_use]
    pub fn into_make_service(self) -> IntoMakeService<Router<S, B>> {
        self.router.into_make_service()
    }

    /// See [`axum::Router::into_make_service_with_connect_info`] for details.
    #[tracing::instrument(skip_all)]
    #[must_use]
    pub fn into_make_service_with_connect_info<C>(
        self,
    ) -> IntoMakeServiceWithConnectInfo<Router<S, B>, C> {
        self.router.into_make_service_with_connect_info()
    }
}

impl<S, B> From<Router<S, B>> for ApiRouter<S, B> {
    fn from(router: Router<S, B>) -> Self {
        ApiRouter {
            paths: IndexMap::new(),
            router,
        }
    }
}

impl<S, B> From<ApiRouter<S, B>> for Router<S, B> {
    fn from(api: ApiRouter<S, B>) -> Self {
        api.router
    }
}

/// Convenience extension trait for [`axum::Router`].
pub trait RouterExt<S, B>: private::Sealed + Sized {
    /// Turn the router into an [`ApiRouter`] to enable
    /// automatic generation of API documentation.
    fn into_api(self) -> ApiRouter<S, B>;
    /// Add an API route, see [`ApiRouter::api_route`](crate::axum::ApiRouter::api_route)
    /// for details.
    ///
    /// This method additionally turns the router into an [`ApiRouter`].
    fn api_route(self, path: &str, method_router: ApiMethodRouter<S, B>) -> ApiRouter<S, B>;
}

impl<S, B> RouterExt<S, B> for Router<S, B>
where
    B: HttpBody + Send + 'static,
    S: Send + Sync + 'static,
{
    #[tracing::instrument(skip_all)]
    fn into_api(self) -> ApiRouter<S, B> {
        ApiRouter::from(self)
    }

    #[tracing::instrument(skip_all)]
    fn api_route(self, path: &str, method_router: ApiMethodRouter<S, B>) -> ApiRouter<S, B> {
        ApiRouter::from(self).api_route(path, method_router)
    }
}

impl<S, B> private::Sealed for Router<S, B> {}

mod private {
    pub trait Sealed {}
}

#[doc(hidden)]
pub enum ServiceOrApiRouter<S, B, T> {
    Service(T),
    Router(ApiRouter<S, B>),
}

impl<T, S, B> From<T> for ServiceOrApiRouter<S, B, T>
where
    T: Service<Request<B>, Error = Infallible> + Clone + Send + 'static,
    T::Response: IntoResponse,
    T::Future: Send + 'static,
{
    fn from(v: T) -> Self {
        Self::Service(v)
    }
}

impl<S, B> From<ApiRouter<S, B>> for ServiceOrApiRouter<S, B, DefinitelyNotService> {
    fn from(v: ApiRouter<S, B>) -> Self {
        Self::Router(v)
    }
}

// To help with type-inference.
#[derive(Clone)]
#[doc(hidden)]
pub enum DefinitelyNotService {}

impl<B> Service<Request<B>> for DefinitelyNotService {
    type Response = String;

    type Error = Infallible;

    type Future =
        Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send + Sync + 'static>>;

    fn poll_ready(
        &mut self,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        unreachable!()
    }

    fn call(&mut self, _req: Request<B>) -> Self::Future {
        unreachable!()
    }
}