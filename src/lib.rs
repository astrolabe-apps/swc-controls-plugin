mod utils;
use swc_core::common::SyntaxContext;
#[cfg(test)]
use swc_core::ecma::visit::visit_mut_pass;
use utils::*;

use std::{
    borrow::BorrowMut,
    fmt::Debug,
    ops::{Deref, DerefMut},
};

use regex::Regex;
use std::path::PathBuf;
use swc_core::{
    common::comments::Comments,
    common::{comments::CommentKind, sync::Lazy, Span, DUMMY_SP},
    ecma::{
        ast::*,
        atoms::Atom,
        utils::{prepend_stmt, private_ident},
        visit::{noop_visit_mut_type, VisitMut, VisitMutWith},
    },
    plugin::{
        metadata::TransformPluginMetadataContextKind, plugin_transform,
        proxies::TransformPluginProgramMetadata,
    },
};

fn is_track_signals_directive(string: &str) -> bool {
    // https://github.com/preactjs/signals/blob/e04671469e9272de356109170b2e429db49db2f0/packages/react-transform/src/index.ts#L18
    static RE: Lazy<Regex> = Lazy::new(|| Regex::new(r#"(\s|^)@trackControls(\s|$)"#).unwrap());

    RE.is_match(string)
}
fn is_no_track_signals_directive(string: &str) -> bool {
    static RE: Lazy<Regex> = Lazy::new(|| Regex::new(r#"(\s|^)@noTrackControls(\s|$)"#).unwrap());

    RE.is_match(string)
}

trait StrExt {
    fn from_str(str: &str) -> Str;
}
impl StrExt for Str {
    fn from_str(str: &str) -> Str {
        Str {
            span: DUMMY_SP,
            value: Atom::new(str).into(),
            raw: None,
        }
    }
}
trait IdentExt {
    fn use_signals(ctxt: SyntaxContext) -> Ident;
}
impl IdentExt for Ident {
    fn use_signals(ctxt: SyntaxContext) -> Ident {
        Ident {
            span: DUMMY_SP,
            sym: "useComponentTracking".into(),
            ctxt,
            optional: false,
        }
    }
}

mod options {
    use serde::Deserialize;

    #[derive(PartialEq, Eq, Deserialize, Default)]
    #[serde(rename_all = "kebab-case")]
    pub enum TransformMode {
        Manual,
        /**
         * all options affects only components
         */
        #[default]
        All,
        Auto,
    }

    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct PreactSignalsPluginExperimental {
        #[serde(default)]
        pub add_hook_usage_flag: bool,
    }
    impl Default for PreactSignalsPluginExperimental {
        fn default() -> Self {
            Self {
                add_hook_usage_flag: false,
            }
        }
    }
    fn default_import_source() -> String {
        "@react-typed-forms/core".into()
    }
    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct PreactSignalsPluginOptions {
        #[serde(default)]
        pub mode: TransformMode,
        #[serde(default = "default_import_source")]
        pub import_source: String,
        #[serde(default)]
        pub experimental: PreactSignalsPluginExperimental,
    }

    impl Default for PreactSignalsPluginOptions {
        fn default() -> Self {
            PreactSignalsPluginOptions {
                mode: TransformMode::default(),
                import_source: default_import_source(),
                experimental: PreactSignalsPluginExperimental::default(),
            }
        }
    }
}
use options::{PreactSignalsPluginOptions, TransformMode};

pub struct SignalsTransformVisitor<C>
where
    C: Comments + Debug,
{
    comments: C,
    mode: TransformMode,
    import_use_signals: Option<Ident>,
    use_signals_import_source: Str,
    ignore_span: Option<Span>,
    file_trackable_name: Option<Trackable>,
    add_context_to_hooks: bool,
    depth: u32, // unresolved_mark: Mark,
}
impl<C> SignalsTransformVisitor<C>
where
    C: Comments + Debug,
{
    fn is_top_level_component(&self) -> bool {
        self.depth == 1
    }

    fn get_import_use_signals(&mut self) -> Ident {
        self.import_use_signals
            .get_or_insert(private_ident!("_useComponentTracking"))
            .clone()
    }
    fn from_options(
        options: PreactSignalsPluginOptions,
        comments: C,
        file_trackable_name: Option<Trackable>,
        // unresolved_mark: Mark,
    ) -> Self {
        SignalsTransformVisitor {
            comments,
            file_trackable_name,
            mode: options.mode,
            import_use_signals: None,
            use_signals_import_source: Str::from_str(options.import_source.as_str()),
            ignore_span: None,
            add_context_to_hooks: options.experimental.add_hook_usage_flag,
            depth: 0,
            // unresolved_mark,
            // context_mark: unresolved_mark,
        }
    }
    fn from_default(
        comments: C,
        file_trackable_name: Option<Trackable>,
        // unresolved_mark: Mark,
    ) -> Self {
        SignalsTransformVisitor::from_options(
            PreactSignalsPluginOptions::default(),
            comments,
            file_trackable_name,
            // unresolved_mark,
        )
    }

    fn process_var_decl(&mut self, n: &mut VarDecl, additional_spans: Option<&[&Span]>) {
        if let Some(first) = n.decls.as_mut_slice().first_mut()
            && let Some(init) = &mut first.init
            && let child_span = init.unwrap_parens().get_span()
            && let Some(mut component) = extract_fn_from_expr(init.unwrap_parens_mut())
            && let defaults_spans = &[&child_span, &n.span]
            && let spans = if let Some(extra_spans) = additional_spans {
                [defaults_spans, extra_spans].concat()
            } else {
                defaults_spans.to_vec()
            }
            && let Some(trackable) = match component.get_fn_ident() {
                None => {
                    self.should_track_option_ident(&spans, Some(&first.name), &component, false)
                }
                Some(ident) => {
                    self.should_track_option_ident(&spans, Some(&ident), &component, false)
                }
            }
        {
            self.track(trackable, &mut component);
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ShouldTrack {
    OptIn,
    OptOut,
    Auto,
}

fn should_track_by_comment<C>(comments: &C, span: &Span) -> ShouldTrack
where
    C: Comments + Debug,
{
    match comments.get_leading(span.lo) {
        Some(item) => {
            let is_track_signals = item
                .iter()
                .find(|it| {
                    it.kind == CommentKind::Block && is_track_signals_directive(it.text.as_str())
                })
                .is_some();
            let is_no_track_signals = item
                .iter()
                .find(|it| {
                    it.kind == CommentKind::Block && is_no_track_signals_directive(it.text.as_str())
                })
                .is_some();

            match (is_track_signals, is_no_track_signals) {
                (true, true) => {
                    // TODO: warn
                    // println!("component uses both @useSignals and @noUseSignals at the same time, ignoring @useSignals");
                    ShouldTrack::OptOut
                }
                (true, false) => ShouldTrack::OptIn,
                (false, true) => ShouldTrack::OptOut,
                _ => ShouldTrack::Auto,
            }
        }
        None => ShouldTrack::Auto,
    }
}

impl<C> SignalsTransformVisitor<C>
where
    C: Comments + Debug,
{
    fn is_trackable<I>(&self, ident: Option<&I>, is_default_export: bool) -> Option<Trackable>
    where
        I: MaybeComponentName,
    {
        if is_default_export && ident.is_none() {
            self.file_trackable_name.to_owned()
        } else {
            ident.and_then(|it| it.is_trackable())
        }
    }

    #[inline]
    fn should_track_option_ident<I, Comp>(
        &self,
        comment_spans: &[&Span],
        ident: Option<&I>,
        component: &Comp,
        is_default_export: bool,
    ) -> Option<Trackable>
    where
        Comp: Detectable,
        I: MaybeComponentName,
    {
        let comments: &C = &self.comments;
        let should_track = comment_spans
            .into_iter()
            .filter_map(|span| match should_track_by_comment(comments, span) {
                ShouldTrack::Auto => None,
                it => Some(it),
            })
            .reduce(|acc, it| match (acc, it) {
                (ShouldTrack::OptIn, ShouldTrack::OptOut) => ShouldTrack::OptOut,
                (ShouldTrack::OptOut, ShouldTrack::OptIn) => ShouldTrack::OptOut,
                (_, it) => it,
            })
            .unwrap_or(ShouldTrack::Auto);

        match should_track {
            ShouldTrack::Auto => {
                let this = &self;
                match this.mode {
                    TransformMode::Manual => None,
                    TransformMode::Auto => match this.is_trackable(ident, is_default_export) {
                        // Some(Trackable::Hook)
                        //     if this.transform_hooks && component.has_dot_value() =>
                        // {
                        //     Some(Trackable::Hook)
                        // }
                        Some(Trackable::Component) if component.has_jsx() => {
                            Some(Trackable::Component)
                        }
                        _ => None,
                    },
                    TransformMode::All => match this.is_trackable(ident, is_default_export) {
                        // Some(Trackable::Hook)
                        //     if this.transform_hooks && component.has_dot_value() =>
                        // {
                        //     Some(Trackable::Hook)
                        // }
                        Some(Trackable::Component) if component.has_jsx() => {
                            Some(Trackable::Component)
                        }
                        _ => None,
                    },
                }
            }
            ShouldTrack::OptIn => Some(
                self.is_trackable(ident, is_default_export)
                    .unwrap_or(Trackable::Unknown),
            ),
            ShouldTrack::OptOut => None,
        }
    }

    #[inline]
    fn track<TWrappable>(&mut self, trackable: Trackable, wrappable: &mut TWrappable)
    where
        TWrappable: SignalWrappable,
    {
        if self.is_top_level_component() {
            wrappable.wrap_with_use_signals(
                self.get_import_use_signals(),
                match self.add_context_to_hooks {
                    false => None,
                    true => Some(trackable),
                },
            )
        }
    }
}
impl<C> VisitMut for SignalsTransformVisitor<C>
where
    C: Comments + Debug,
{
    noop_visit_mut_type!();

    fn visit_mut_var_decl(&mut self, n: &mut VarDecl) {
        self.depth += 1;

        if self.is_top_level_component() {
            let should_process = self
                .ignore_span
                .map(|span| !span.eq(&n.span))
                .unwrap_or(true);

            if should_process {
                self.process_var_decl(n, None)
            }

            n.visit_mut_children_with(self);
        }
        self.depth -= 1;
    }
    
    fn visit_mut_export_decl(&mut self, n: &mut ExportDecl) {
        match n {
            ExportDecl {
                span,
                decl: Decl::Var(var_decl),
            } => {
                self.depth += 1;

                if self.is_top_level_component() {
                    self.process_var_decl(var_decl.deref_mut(), Some(&[&span]));
                    let old_span = self.ignore_span;
                    self.ignore_span = Some(var_decl.span.clone());
                    n.visit_mut_children_with(self);
                    self.ignore_span = old_span
                }

                self.depth -= 1;
            }
            ExportDecl {
                span,
                decl: Decl::Fn(fn_declr),
            } => {
                self.depth += 1;

                if self.is_top_level_component() {
                    self.should_track_option_ident(
                        &[&span, &fn_declr.function.span],
                        Some(&fn_declr.ident),
                        fn_declr,
                        false,
                    )
                    .inspect(|trackable| self.track(trackable.clone(), &mut *fn_declr.function));

                    let old_span = self.ignore_span;
                    self.ignore_span = Some(fn_declr.function.span.clone());
                    n.visit_mut_children_with(self);
                    self.ignore_span = old_span
                }

                self.depth -= 1;
            }
            n => {
                self.depth += 1;

                if self.is_top_level_component() {
                    n.visit_mut_children_with(self);
                }

                self.depth -= 1;
            }
        }
    }
    fn visit_mut_export_default_decl(&mut self, n: &mut ExportDefaultDecl) {
        match n {
            ExportDefaultDecl {
                span,
                decl: DefaultDecl::Fn(fn_expr),
            } => {
                self.depth += 1;

                if self.is_top_level_component() {
                    if let Some(trackable) = self.should_track_option_ident(
                        &[&span, &fn_expr.function.span],
                        fn_expr.ident.as_ref(),
                        fn_expr,
                        true,
                    ) {
                        self.track(trackable, &mut *fn_expr.function);
                    }
                    let old_span = self.ignore_span;
                    self.ignore_span = Some(fn_expr.function.span.clone());
                    n.visit_mut_children_with(self);
                    self.ignore_span = old_span
                }

                self.depth -= 1;
            }
            n => {
                self.depth += 1;
                if self.is_top_level_component() {
                    n.visit_mut_children_with(self);
                }
                self.depth -= 1;
            }
        }
    }

    fn visit_mut_export_default_expr(&mut self, n: &mut ExportDefaultExpr) {
        self.depth += 1;

        if self.is_top_level_component() {
            let ExportDefaultExpr { expr, span } = n;
            let child_span = expr.unwrap_parens().get_span();

            if let Some(mut component) = extract_fn_from_expr(expr.unwrap_parens_mut()) {
                self.should_track_option_ident(
                    &[&span, &child_span],
                    component.get_fn_ident().as_ref(),
                    &component,
                    true,
                )
                .inspect(|trackable| self.track(trackable.clone(), &mut component));
            }

            n.visit_mut_children_with(self);

            // let old_span = self.ignore_span;
            // self.ignore_span = Some(child_span);
            // self.ignore_span = old_span
        }

        self.depth -= 1;
    }

    fn visit_mut_fn_decl(&mut self, n: &mut FnDecl) {
        self.depth += 1;

        if self.is_top_level_component() {
            if match self.ignore_span {
                Some(span) => !span.eq(&n.function.span),
                None => true,
            } && let Some(trackable) =
                self.should_track_option_ident(&[&n.function.span], Some(&n.ident), n, false)
            {
                self.track(trackable, &mut *n.function)
            }
            n.visit_mut_children_with(self);
        }

        self.depth -= 1;
    }

    fn visit_mut_assign_expr(&mut self, n: &mut AssignExpr) {
        self.depth += 1;

        if self.is_top_level_component() {
            if let Some(mut component) = extract_fn_from_expr(n.right.borrow_mut())
                && let Some(trackable) = match component.get_fn_ident() {
                    None => {
                        self.should_track_option_ident(&[&n.span], Some(&n.left), &component, false)
                    }
                    Some(ident) => {
                        self.should_track_option_ident(&[&n.span], Some(&ident), &component, false)
                    }
                }
            {
                self.track(trackable, &mut component);
            }

            n.visit_mut_children_with(self);
        }

        self.depth -= 1;
    }

    fn visit_mut_key_value_prop(&mut self, n: &mut KeyValueProp) {
        self.depth += 1;

        if self.is_top_level_component() {
            if let Some(mut component) = extract_fn_from_expr(&mut n.value)
                && let Some(trackable) = self.should_track_option_ident(
                    &[&n.key.get_span()],
                    Some(
                        &component
                            .get_fn_ident()
                            .map_or(n.key.clone(), |it| PropName::Ident(it.into())),
                    ),
                    &component,
                    false,
                )
            {
                self.track(trackable, &mut component);
            }

            n.visit_mut_children_with(self);
        }

        self.depth -= 1;
    }

    fn visit_mut_method_prop(&mut self, n: &mut MethodProp) {
        self.depth += 1;

        if self.is_top_level_component() {
            if let Some(trackable) = self.should_track_option_ident(
                &[&n.function.span, &n.key.get_span()],
                Some(&n.key),
                n.function.deref(),
                false,
            ) {
                self.track(trackable, &mut *n.function);
            }

            n.visit_mut_children_with(self);
        }

        self.depth -= 1;
    }

    fn visit_mut_module(&mut self, n: &mut Module) {
        self.import_use_signals = None;
        n.visit_mut_children_with(self);

        if let Some(ident) = &self.import_use_signals {
            prepend_stmt(
                &mut n.body,
                ModuleItem::ModuleDecl(
                    add_import(
                        ident.clone(),
                        self.use_signals_import_source.clone(),
                        Some(Ident::use_signals(ident.ctxt)),
                    )
                    .into(),
                ),
            )
        }
    }

    fn visit_mut_script(&mut self, n: &mut Script) {
        self.import_use_signals = None;
        n.visit_mut_children_with(self);

        if let Some(ident) = &self.import_use_signals {
            prepend_stmt(
                &mut n.body,
                add_require(
                    ident.clone(),
                    self.use_signals_import_source.clone(),
                    Some(Ident::use_signals(ident.ctxt)),
                    ident.ctxt,
                ),
            )
        }
    }
}

#[plugin_transform]
pub fn process_transform(
    mut program: Program,
    _metadata: TransformPluginProgramMetadata,
) -> Program {
    // _metadata.mark
    program.visit_mut_with(
        &mut ({
            let data = _metadata.get_transform_plugin_config();

            let file_has_trackable_name = _metadata
                .get_context(&TransformPluginMetadataContextKind::Filename)
                .map(|it| PathBuf::from(it))
                .and_then(|it| {
                    it.file_name()
                        .and_then(|it| it.to_str())
                        .and_then(|it| it.is_trackable())
                });

            use serde_json;
            match data {
                Some(data) => {
                    let options = serde_json::from_str::<PreactSignalsPluginOptions>(data.as_str())
                        .expect("transform plugin config should be valid json");
                    SignalsTransformVisitor::from_options(
                        options,
                        _metadata.comments,
                        file_has_trackable_name,
                        // _metadata.unresolved_mark,
                    )
                }
                None => SignalsTransformVisitor::from_default(
                    _metadata.comments,
                    file_has_trackable_name,
                    // _metadata.unresolved_mark,
                ),
            }
        }),
    );
    program
}

#[cfg(test)]
fn get_syntax() -> swc_core::ecma::parser::Syntax {
    use swc_core::ecma::parser::{EsSyntax, Syntax};

    let mut a = EsSyntax::default();
    a.jsx = true;
    Syntax::Es(a)
}

macro_rules! test_inline {
    (ignore, $syntax:expr, $tr:expr, $test_name:ident, $input:expr, $output:expr) => {
        #[test]
        #[ignore]
        fn $test_name() {
            use swc_core::ecma::transforms::testing::test_inline_input_output;
            // defaulting to module
            test_inline_input_output($syntax, Some(true), $tr, $input, $output)
        }
    };

    ($syntax:expr, $tr:expr, $test_name:ident, $input:expr, $output:expr) => {
        #[test]
        fn $test_name() {
            use swc_core::ecma::transforms::testing::test_inline_input_output;
            // defaulting to module
            test_inline_input_output($syntax, Some(true), $tr, $input, $output)
        }
    };
}

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    nested_components,
    // Input codes
    r#"
    function Asdjsadf() {
        const outerControl = useControl(false)
        var someControl = useControl(true)
        function B() {
            const control = useControl("")
            return <div />
        };
        function c() {
            return 5
        };
        return <div />
    }
    export default function AnotherComponent(){
    var someValue = useControl("")
      return <div>AnotherComponent</div>
    }
    export function OtherComponets(){
     return <div>OtherComponets</div>
    }
    "#,
    // Expected codes
    r#"
    import { useComponentTracking as _useComponentTracking } from "@react-typed-forms/core";
    function Asdjsadf() {
        var stop = _useComponentTracking();
        try {
            const outerControl = useControl(false);
            var someControl = useControl(true)
            function B() {
                const control = useControl("");
                return <div/>;
            }
            ;
            function c() {
                return 5;
            }
            ;
            return <div/>;
        } finally{
            stop();
        }
    }
export default function AnotherComponent(){
var stop = _useComponentTracking();
    try {
     var someValue = useControl("");
        return <div>AnotherComponent</div>;
    } finally{
        stop();
    }
}
 export function OtherComponets(){
  var stop = _useComponentTracking();
  try{
      return <div>OtherComponets</div>
  }finally{
      stop();
  }
}

"#
);

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    hocs,
    // Input codes
    r#"
const Cec = memo(() => {
    return <div />
})
// hocs should be transformed
const Cyc = React.lazy(React.memo(() => {
    return <div />
}), {})
"#,
    // Expected codes
    r#"
const Cec = memo(()=>{
    return <div/>;
});
const Cyc = React.lazy(React.memo(()=>{
    return <div/>;
}), {});
"#
);

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    arrow_fn,
    // Input codes
    r#"
const A = () => {
    return <div />
}
const Cecek = () => <div />
"#,
    // Expected codes
    r#"
import { useComponentTracking as _useComponentTracking } from "@react-typed-forms/core";
const A = ()=>{
    var stop = _useComponentTracking();
    try {
        return <div/>;
    } finally{
        stop();
    }
};
const Cecek = ()=>{
    var stop = _useComponentTracking();
    try {
        return <div/>;
    } finally{
        stop();
    }
};
"#
);

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    function,
    // Input codes
    r#"
// should be transformed
function A(){
    return <div />
}
"#,
    // Expected codes
    r#"
import { useComponentTracking as _useComponentTracking } from "@react-typed-forms/core";
function A() {
    var stop = _useComponentTracking();
    try {
        return <div/>;
    } finally{
        stop();
    }
}
"#
);

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    function_expr,
    // Input codes
    r#"
var C = function(){
    return <div />
};
var C2 = function C3(){
    return <div />
};
"#,
    // Expected codes
    r#"
import { useComponentTracking as _useComponentTracking } from "@react-typed-forms/core";
var C = function() {
    var stop = _useComponentTracking();
    try {
        return <div/>;
    } finally{
        stop();
    }
};
var C2 = function C3() {
    var stop = _useComponentTracking();
    try {
        return <div/>;
    } finally{
        stop();
    }
};
"#
);

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    opt_in,
    // Input codes
    r#"
/**
 * @trackControls
 */
function a(){
    return 10;
}

/**
 * @trackControls
 */
const b = () => {
    return 10;
}

/**
 * @trackControls
 */
const c = function(){
    return 10
};
/**
 * @trackControls
 */
const d = () => 10

/**
 * @trackControls
 */
export function boba(){
    return 10
}

/**
 * @trackControls
 */
export const boba2 = () => 10
"#,
    // Expected codes
    r#"
import { useComponentTracking as _useComponentTracking } from "@react-typed-forms/core";
function a() {
    var stop = _useComponentTracking();
    try {
        return 10;
    } finally{
        stop();
    }
}
const b = ()=>{
    var stop = _useComponentTracking();
    try {
        return 10;
    } finally{
        stop();
    }
};
const c = function() {
    var stop = _useComponentTracking();
    try {
        return 10;
    } finally{
        stop();
    }
};
const d = ()=>{
    var stop = _useComponentTracking();
    try {
        return 10;
    } finally{
        stop();
    }
};

export function boba() {
    var stop = _useComponentTracking();
    try {
        return 10;
    } finally{
        stop();
    }
}
export const boba2 = ()=>{
    var stop = _useComponentTracking();
    try {
        return 10;
    } finally{
        stop();
    }
};
"#
);

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    opt_in_opt_out,
    // Input codes
    r#"
/**
 * @noTrackControls
 * @trackControls
 */
function MyComponent() {
    return <div>{signal.value}</div>;
}
"#,
    // Expected codes
    r#"
function MyComponent() {
    return <div>{signal.value}</div>;
}
"#
);

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    rare_components,
    // Note: components in object literals (methods, properties, computed
    // keys) are NOT wrapped — only plain assignment expressions are.
    // Input codes
    r#"
let Jopa;
Jopa = () => <>{a.value}</>
Jopa = function(){
    return <>{a.value}</>
}
const A = {
    Beb(){
        return <>10</>
    }
}

A.bebe.Baba = () => <div>{a.value}</div>

const Beb = {
    A: () => <div />
}

const _ = {
    ['Aboba']() {
        return <div />
    }
}
    "#,
    // Expected codes
    r#"
import { useComponentTracking as _useComponentTracking } from "@react-typed-forms/core";

let Jopa;
Jopa = ()=>{
    var stop = _useComponentTracking();
    try {
        return <>{a.value}</>;
    } finally{
        stop();
    }
};
Jopa = function() {
    var stop = _useComponentTracking();
    try {
        return <>{a.value}</>;
    } finally{
        stop();
    }
};
const A = {
    Beb() {
        return <>10</>;
    }
};
A.bebe.Baba = ()=>{
    var stop = _useComponentTracking();
    try {
        return <div>{a.value}</div>;
    } finally{
        stop();
    }
};
const Beb = {
    A: ()=><div/>
};

const _ = {
    ['Aboba']() {
        return <div/>;
    }
}
"#
);

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        Some(Trackable::Component)
    )),
    default_components,
    // Input codes
    r#"
export default function(){
    return <div />
}
export default (() => {
    return <div />
})
"#,
    // Expected codes
    r#"
import { useComponentTracking as _useComponentTracking } from "@react-typed-forms/core";
export default function() {
    var stop = _useComponentTracking();
    try {
        return <div/>;
    } finally{
        stop();
    }
}

export default (()=>{
    var stop = _useComponentTracking();
    try {
        return <div/>;
    } finally{
        stop();
    }
});
"#
);

test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    import_goes_after_directives,
    // Input codes
    r#"
'use strict';

const Bebe = () => <div>{a.value}</div>
"#,
    // Expected codes
    r#"
'use strict';

import { useComponentTracking as _useComponentTracking } from "@react-typed-forms/core";
const Bebe = ()=>{
    var stop = _useComponentTracking();
    try {
        return <div>{a.value}</div>;
    } finally{
        stop();
    }
}
"#
);

// Hooks are intentionally NOT transformed (the old transformHooks behavior
// was removed) — even when they read control values.
test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_default(
        tester.comments.clone(),
        None
    )),
    hooks_are_not_transformed,
    // Input codes
    r#"
const useAboba = () => a.value
function useBeb() {
    const counter = useControl(0);
    return counter;
}
"#,
    // Expected codes
    r#"
const useAboba = () => a.value
function useBeb() {
    const counter = useControl(0);
    return counter;
}
"#
);

// experimental.addHookUsageFlag passes the trackable kind as an argument:
// component -> 1, hook (opt-in only) -> 2, unknown opt-in -> bare call
// without try/finally.
test_inline!(
    get_syntax(),
    |tester| visit_mut_pass(SignalsTransformVisitor::from_options(
        serde_json::from_str::<PreactSignalsPluginOptions>(
            r#"{"experimental":{"addHookUsageFlag":true}}"#
        )
        .unwrap(),
        tester.comments.clone(),
        None
    )),
    hook_usage_flag,
    // Input codes
    r#"
/**
 * @trackControls
 */
const useAboba = () => {
    return a.b;
}
/**
 * @trackControls
 */
const unknown = () => undefined
const Component = () => {
    return <></>
}
"#,
    // Expected codes
    r#"
import { useComponentTracking as _useComponentTracking } from "@react-typed-forms/core";
const useAboba = ()=>{
    var stop = _useComponentTracking(2);
    try {
        return a.b;
    } finally{
        stop();
    }
};
const unknown = ()=>{
    _useComponentTracking();
    return undefined;
};
const Component = ()=>{
    var stop = _useComponentTracking(1);
    try {
        return <></>;
    } finally{
        stop();
    }
};
"#
);
