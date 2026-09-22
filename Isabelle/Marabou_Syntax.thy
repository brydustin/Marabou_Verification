theory Marabou_Syntax
  imports "HOL.Real"
begin

text \<open>
  An abstract real-arithmetic fragment, not a model of C++ storage or rounding.
  Source references are relative to upstream/Marabou at the revision recorded
  in notes/MARABOU_SOURCE_MAP.md.
\<close>

type_synonym var = nat
type_synonym valuation = "var \<Rightarrow> real"

text \<open>
  Finite lists of coefficient/variable pairs deliberately allow repeated variables
  and zero coefficients. See src/engine/Equation.h (Equation::Addend) and
  src/common/LinearExpression.h (LinearExpression). The constant is explicit.
\<close>

datatype linexpr = Linexpr real "(real \<times> var) list"

datatype linear_constraint =
    LinearEq linexpr real
  | LinearLe linexpr real
  | LinearGe linexpr real

text \<open>
  Equation::EQ/LE/GE are in src/engine/Equation.h. Bounds correspond to
  src/engine/Tightening.h (LB/UB), but are propositions here, not mutations.
  Absence of a bound represents an unbounded direction; infinities are not reals.
\<close>

datatype bound = Lower var real | Upper var real
datatype relu_constraint = ReLU var var

text \<open>
  ReLU b f corresponds to src/engine/ReluConstraint.h (ReluConstraint(b,f)).
  The query is a finite conjunction inspired by InputQuery/Query in
  src/engine/InputQuery.h and src/engine/Query.h. No variable-count restriction,
  parser, incremental state, other activations, or preprocessing is modeled.
\<close>

record query =
  linear_atoms :: "linear_constraint list"
  query_bounds :: "bound list"
  relu_atoms :: "relu_constraint list"

end
