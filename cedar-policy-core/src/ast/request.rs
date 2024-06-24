/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use crate::entities::json::{
    ContextJsonDeserializationError, ContextJsonParser, NullContextSchema,
};
use crate::evaluator::{EvaluationError, RestrictedEvaluator};
use crate::extensions::Extensions;
use crate::parser::Loc;
use crate::ast::proto;
use miette::Diagnostic;
use serde::Serialize;
use smol_str::SmolStr;
use std::sync::Arc;
use thiserror::Error;

use super::{
    BorrowedRestrictedExpr, EntityUID, Expr, ExprKind, ExpressionConstructionError, PartialValue,
    PartialValueSerializedAsExpr, RestrictedExpr, Unknown, Value, ValueKind, Var,
};

/// Represents the request tuple <P, A, R, C> (see the Cedar design doc).
#[derive(Debug, Clone, Serialize)]
pub struct Request {
    /// Principal associated with the request
    pub(crate) principal: EntityUIDEntry,

    /// Action associated with the request
    pub(crate) action: EntityUIDEntry,

    /// Resource associated with the request
    pub(crate) resource: EntityUIDEntry,

    /// Context associated with the request.
    /// `None` means that variable will result in a residual for partial evaluation.
    pub(crate) context: Option<Context>,
}

/// An entry in a request for a Entity UID.
/// It may either be a concrete EUID
/// or an unknown in the case of partial evaluation
#[derive(Debug, Clone, Serialize)]
pub enum EntityUIDEntry {
    /// A concrete (but perhaps unspecified) EntityUID
    Known {
        /// The concrete `EntityUID`
        euid: Arc<EntityUID>,
        /// Source location associated with the `EntityUIDEntry`, if any
        loc: Option<Loc>,
    },
    /// An EntityUID left as unknown for partial evaluation
    Unknown {
        /// Source location associated with the `EntityUIDEntry`, if any
        loc: Option<Loc>,
    },
}

impl EntityUIDEntry {
    /// Evaluate the entry to either:
    /// A value, if the entry is concrete
    /// An unknown corresponding to the passed `var`
    pub fn evaluate(&self, var: Var) -> PartialValue {
        match self {
            EntityUIDEntry::Known { euid, loc } => {
                Value::new(Arc::unwrap_or_clone(Arc::clone(euid)), loc.clone()).into()
            }
            EntityUIDEntry::Unknown { loc } => Expr::unknown(Unknown::new_untyped(var.to_string()))
                .with_maybe_source_loc(loc.clone())
                .into(),
        }
    }

    /// Create an entry with a concrete EntityUID and the given source location
    pub fn concrete(euid: EntityUID, loc: Option<Loc>) -> Self {
        Self::Known {
            euid: Arc::new(euid),
            loc,
        }
    }

    /// Get the UID of the entry, or `None` if it is unknown (partial evaluation)
    pub fn uid(&self) -> Option<&EntityUID> {
        match self {
            Self::Known { euid, .. } => Some(euid),
            Self::Unknown { .. } => None,
        }
    }
}

impl From<proto::EntityUidEntry> for EntityUIDEntry {
    fn from(v: proto::EntityUidEntry) -> Self {
        let loc : Option<Loc> = v.loc.map(Loc::from);
        let ety = proto::entity_uid_entry::EntityUidEntryType::try_from(v.ty).unwrap();

        match ety {
            proto::entity_uid_entry::EntityUidEntryType::Unknown => {
                Self::Unknown { loc: loc }
            }
            proto::entity_uid_entry::EntityUidEntryType::Known => {
                EntityUIDEntry::concrete(EntityUID::from(v.euid.unwrap()), loc)
            }
        }
    }
}

impl From<EntityUIDEntry> for proto::EntityUidEntry {
    fn from(v: EntityUIDEntry) -> Self {
        match v {
            EntityUIDEntry::Unknown { loc } => {
                Self {
                    ty: proto::entity_uid_entry::EntityUidEntryType::Unknown.into(),
                    euid: None,
                    loc: loc.map(proto::Loc::from)
                }
            }
            EntityUIDEntry::Known { euid, loc } => {
                Self {
                    ty: proto::entity_uid_entry::EntityUidEntryType::Known.into(),
                    euid: Some(proto::EntityUid::from(Arc::unwrap_or_clone(euid))),
                    loc: loc.map(proto::Loc::from)
                }
            }
        }
    }
}



impl Request {
    /// Default constructor.
    ///
    /// If `schema` is provided, this constructor validates that this `Request`
    /// complies with the given `schema`.
    pub fn new<S: RequestSchema>(
        principal: (EntityUID, Option<Loc>),
        action: (EntityUID, Option<Loc>),
        resource: (EntityUID, Option<Loc>),
        context: Context,
        schema: Option<&S>,
        extensions: Extensions<'_>,
    ) -> Result<Self, S::Error> {
        let req = Self {
            principal: EntityUIDEntry::concrete(principal.0, principal.1),
            action: EntityUIDEntry::concrete(action.0, action.1),
            resource: EntityUIDEntry::concrete(resource.0, resource.1),
            context: Some(context),
        };
        if let Some(schema) = schema {
            schema.validate_request(&req, extensions)?;
        }
        Ok(req)
    }

    /// Create a new `Request` with potentially unknown (for partial eval) variables.
    ///
    /// If `schema` is provided, this constructor validates that this `Request`
    /// complies with the given `schema` (at least to the extent that we can
    /// validate with the given information)
    pub fn new_with_unknowns<S: RequestSchema>(
        principal: EntityUIDEntry,
        action: EntityUIDEntry,
        resource: EntityUIDEntry,
        context: Option<Context>,
        schema: Option<&S>,
        extensions: Extensions<'_>,
    ) -> Result<Self, S::Error> {
        let req = Self {
            principal,
            action,
            resource,
            context,
        };
        if let Some(schema) = schema {
            schema.validate_request(&req, extensions)?;
        }
        Ok(req)
    }

    /// Create a new `Request` with potentially unknown (for partial eval) variables/context
    /// and without schema validation.
    pub fn new_unchecked(
        principal: EntityUIDEntry,
        action: EntityUIDEntry,
        resource: EntityUIDEntry,
        context: Option<Context>,
    ) -> Self {
        Self {
            principal,
            action,
            resource,
            context,
        }
    }

    /// Get the principal associated with the request
    pub fn principal(&self) -> &EntityUIDEntry {
        &self.principal
    }

    /// Get the action associated with the request
    pub fn action(&self) -> &EntityUIDEntry {
        &self.action
    }

    /// Get the resource associated with the request
    pub fn resource(&self) -> &EntityUIDEntry {
        &self.resource
    }

    /// Get the context associated with the request
    /// Returning `None` means the variable is unknown, and will result in a residual expression
    pub fn context(&self) -> Option<&Context> {
        self.context.as_ref()
    }
}

impl std::fmt::Display for Request {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let display_euid = |maybe_euid: &EntityUIDEntry| match maybe_euid {
            EntityUIDEntry::Known { euid, .. } => format!("{euid}"),
            EntityUIDEntry::Unknown { .. } => "unknown".to_string(),
        };
        write!(
            f,
            "request with principal {}, action {}, resource {}, and context {}",
            display_euid(&self.principal),
            display_euid(&self.action),
            display_euid(&self.resource),
            match &self.context {
                Some(x) => format!("{x}"),
                None => "unknown".to_string(),
            }
        )
    }
}

impl From<proto::Request> for Request {
    fn from(v: proto::Request) -> Self {
        Request::new_unchecked(
            EntityUIDEntry::from(v.principal.unwrap()),
            EntityUIDEntry::from(v.action.unwrap()),
            EntityUIDEntry::from(v.resource.unwrap()),
            v.context.map(Context::from)
        )
    }
}

impl From<Request> for proto::Request {
    fn from(v: Request) -> Self {
        Self {
            principal: Some(proto::EntityUidEntry::from(v.principal)),
            action: Some(proto::EntityUidEntry::from(v.action)),
            resource: Some(proto::EntityUidEntry::from(v.resource)),
            context: v.context.map(proto::Context::from)
        }
    }
}

/// `Context` field of a `Request`
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Context {
    /// Context is internally represented as a `PartialValue`
    ///
    /// Context is serialized as a `RestrictedExpr`, for partly historical reasons.
    //
    // INVARIANT(ContextRecord): This must be a `Record`: either
    // `PartialValue::Value(Value::Record)`, or
    // `PartialValue::Residual(Expr::Record)`, or an appropriate unknown
    #[serde(flatten)]
    context: PartialValueSerializedAsExpr,
}

impl Context {
    /// Create an empty `Context`
    //
    // INVARIANT(ContextRecord): via invariant on `Self::from_pairs`
    pub fn empty() -> Self {
        Self {
            context: PartialValue::Value(Value::empty_record(None)).into(),
        }
    }

    /// Create a `Context` from a `RestrictedExpr`, which must be a `Record`.
    ///
    /// `extensions` provides the `Extensions` which should be active for
    /// evaluating the `RestrictedExpr`.
    //
    // INVARIANT(ContextRecord): always constructs a record if it returns Ok
    pub fn from_expr(
        expr: BorrowedRestrictedExpr<'_>,
        extensions: Extensions<'_>,
    ) -> Result<Self, ContextCreationError> {
        match expr.expr_kind() {
            // INVARIANT(ContextRecord): guaranteed by the match case
            ExprKind::Record { .. } => {
                let evaluator = RestrictedEvaluator::new(&extensions);
                let pval = evaluator.partial_interpret(expr)?;
                Ok(Self {
                    context: pval.into(),
                })
            }
            _ => Err(ContextCreationError::not_a_record(expr.to_owned())),
        }
    }

    /// Create a `Context` from a map of key to `RestrictedExpr`, or a Vec of
    /// `(key, RestrictedExpr)` pairs, or any other iterator of `(key, RestrictedExpr)` pairs
    ///
    /// `extensions` provides the `Extensions` which should be active for
    /// evaluating the `RestrictedExpr`.
    //
    // INVARIANT(ContextRecord): always constructs a record if it returns Ok
    pub fn from_pairs(
        pairs: impl IntoIterator<Item = (SmolStr, RestrictedExpr)>,
        extensions: Extensions<'_>,
    ) -> Result<Self, ContextCreationError> {
        // INVARIANT(ContextRecord): via invariant on `Self::from_expr`
        Self::from_expr(RestrictedExpr::record(pairs)?.as_borrowed(), extensions)
    }

    /// Create a `Context` from a string containing JSON (which must be a JSON
    /// object, not any other JSON type, or you will get an error here).
    /// JSON here must use the `__entity` and `__extn` escapes for entity
    /// references, extension values, etc.
    ///
    /// For schema-based parsing, use `ContextJsonParser`.
    pub fn from_json_str(json: &str) -> Result<Self, ContextJsonDeserializationError> {
        // INVARIANT `.from_json_str` always produces an expression of variant `Record`
        ContextJsonParser::new(None::<&NullContextSchema>, Extensions::all_available())
            .from_json_str(json)
    }

    /// Create a `Context` from a `serde_json::Value` (which must be a JSON
    /// object, not any other JSON type, or you will get an error here).
    /// JSON here must use the `__entity` and `__extn` escapes for entity
    /// references, extension values, etc.
    ///
    /// For schema-based parsing, use `ContextJsonParser`.
    pub fn from_json_value(
        json: serde_json::Value,
    ) -> Result<Self, ContextJsonDeserializationError> {
        // INVARIANT `.from_json_value` always produces an expression of variant `Record`
        ContextJsonParser::new(None::<&NullContextSchema>, Extensions::all_available())
            .from_json_value(json)
    }

    /// Create a `Context` from a JSON file.  The JSON file must contain a JSON
    /// object, not any other JSON type, or you will get an error here.
    /// JSON here must use the `__entity` and `__extn` escapes for entity
    /// references, extension values, etc.
    ///
    /// For schema-based parsing, use `ContextJsonParser`.
    pub fn from_json_file(
        json: impl std::io::Read,
    ) -> Result<Self, ContextJsonDeserializationError> {
        // INVARIANT `.from_json_file` always produces an expression of variant `Record`
        ContextJsonParser::new(None::<&NullContextSchema>, Extensions::all_available())
            .from_json_file(json)
    }

    /// Iterate over the (key, value) pairs in the `Context`; or return `None`
    /// if the `Context` is purely unknown
    //
    // PANIC SAFETY: This is safe due to the invariant on `self.context`, `self.context` must always be a record
    pub fn iter<'s>(&'s self) -> Option<Box<dyn Iterator<Item = (&SmolStr, PartialValue)> + 's>> {
        // PANIC SAFETY invariant on `self.context` ensures that it is a record
        #[allow(clippy::panic)]
        match self.context.as_ref() {
            PartialValue::Value(Value {
                value: ValueKind::Record(record),
                ..
            }) => Some(Box::new(
                record
                    .iter()
                    .map(|(k, v)| (k, PartialValue::Value(v.clone()))),
            )),
            PartialValue::Residual(expr) => match expr.expr_kind() {
                ExprKind::Record(map) => Some(Box::new(
                    map.iter()
                        .map(|(k, v)| (k, PartialValue::Residual(v.clone()))),
                )),
                ExprKind::Unknown(_) => None,
                kind => panic!("internal invariant violation: expected a record, got {kind:?}"),
            },
            v => panic!("internal invariant violation: expected a record, got {v:?}"),
        }
    }
}

impl AsRef<PartialValue> for Context {
    fn as_ref(&self) -> &PartialValue {
        &self.context
    }
}

impl From<Context> for PartialValue {
    fn from(ctx: Context) -> PartialValue {
        ctx.context.into()
    }
}

impl std::default::Default for Context {
    fn default() -> Context {
        Context::empty()
    }
}

impl std::fmt::Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.context)
    }
}

impl From<proto::Context> for Context {
    fn from(v: proto::Context) -> Self {
        Context::from_expr(
            BorrowedRestrictedExpr::new(&Expr::from(v.context.unwrap())).unwrap(),
            Extensions::none()
        ).unwrap()
    }
}

impl From<Context> for proto::Context {
    fn from(v: Context) -> Self {
        Self {
            context: Some(Expr::from(PartialValue::from(v.context)).into())
        }
    }
}

/// Errors while trying to create a `Context`
#[derive(Debug, Diagnostic, Error)]
pub enum ContextCreationError {
    /// Tried to create a `Context` out of something other than a record
    #[error(transparent)]
    #[diagnostic(transparent)]
    NotARecord(#[from] context_creation_errors::NotARecord),
    /// Error evaluating the expression given for the `Context`
    #[error(transparent)]
    #[diagnostic(transparent)]
    Evaluation(#[from] EvaluationError),
    /// Error constructing the expression given for the `Context`.
    /// Only returned by `Context::from_pairs()`
    #[error(transparent)]
    #[diagnostic(transparent)]
    ExpressionConstruction(#[from] ExpressionConstructionError),
}

impl ContextCreationError {
    pub(crate) fn not_a_record(expr: RestrictedExpr) -> Self {
        Self::NotARecord(context_creation_errors::NotARecord {
            expr: Box::new(expr),
        })
    }
}

/// Error subtypes for [`ContextCreationError`]
pub mod context_creation_errors {
    use super::RestrictedExpr;
    use miette::Diagnostic;
    use thiserror::Error;

    /// Error type for an expression that needed to be a record, but is not
    //
    // CAUTION: this type is publicly exported in `cedar-policy`.
    // Don't make fields `pub`, don't make breaking changes, and use caution
    // when adding public methods.
    #[derive(Debug, Error)]
    #[error("expression is not a record: {expr}")]
    pub struct NotARecord {
        /// Expression which is not a record
        pub(super) expr: Box<RestrictedExpr>,
    }

    // custom impl of `Diagnostic`: take source location from the `expr` field
    impl Diagnostic for NotARecord {
        fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
            self.expr.source_loc().map(|loc| {
                Box::new(std::iter::once(miette::LabeledSpan::underline(loc.span)))
                    as Box<dyn Iterator<Item = _>>
            })
        }

        fn source_code(&self) -> Option<&dyn miette::SourceCode> {
            self.expr
                .source_loc()
                .map(|loc| &loc.src as &dyn miette::SourceCode)
        }
    }
}

/// Trait for schemas capable of validating `Request`s
pub trait RequestSchema {
    /// Error type returned when a request fails validation
    type Error: miette::Diagnostic;
    /// Validate the given `request`, returning `Err` if it fails validation
    fn validate_request(
        &self,
        request: &Request,
        extensions: Extensions<'_>,
    ) -> Result<(), Self::Error>;
}

/// A `RequestSchema` that does no validation and always reports a passing result
#[derive(Debug, Clone)]
pub struct RequestSchemaAllPass;
impl RequestSchema for RequestSchemaAllPass {
    type Error = Infallible;
    fn validate_request(
        &self,
        _request: &Request,
        _extensions: Extensions<'_>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// Wrapper around `std::convert::Infallible` which also implements
/// `miette::Diagnostic`
#[derive(Debug, Diagnostic, Error)]
#[error(transparent)]
pub struct Infallible(pub std::convert::Infallible);

#[cfg(test)]
mod test {
    use super::*;
    use cool_asserts::assert_matches;

    #[test]
    fn test_json_from_str_non_record() {
        assert_matches!(
            Context::from_expr(RestrictedExpr::val("1").as_borrowed(), Extensions::none()),
            Err(ContextCreationError::NotARecord { .. })
        );
        assert_matches!(
            Context::from_json_str("1"),
            Err(ContextJsonDeserializationError::ContextCreation(
                ContextCreationError::NotARecord { .. }
            ))
        );
    }

    #[test]
    fn protobuf_roundtrip() {
        let context: Context = Context::from_expr(
            RestrictedExpr::record([
                    ("foo".into(), RestrictedExpr::val(37),)
                ])
                .expect("Error creating restricted record.")
                .as_borrowed()
            ,
            Extensions::none()
        ).expect("Error creating context");
        let request = Request::new_unchecked(
            EntityUIDEntry::Known{ euid: Arc::new(EntityUID::with_eid("andrew")), loc: None },
            EntityUIDEntry::Known { euid: Arc::new(EntityUID::with_eid("read")), loc: None },
            EntityUIDEntry::Known { euid: Arc::new(EntityUID::with_eid("book")), loc: None },
            Some(context.clone())
        );
        let request_roundtrip: Request = Request::from(proto::Request::from(request.clone()));
        assert_eq!(context, Context::from(proto::Context::from(context.clone())));
        assert_matches!(request_roundtrip.principal, EntityUIDEntry::Known{ euid: _, loc: _ });
        assert_matches!(request_roundtrip.action, EntityUIDEntry::Known{ euid: _, loc: _ });
        assert_matches!(request_roundtrip.resource, EntityUIDEntry::Known{ euid: _, loc: _ });
    }
}
