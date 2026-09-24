theory Tableau_Initialization_Examples
  imports Tableau_Initial_Basis Imported_Marabou_Initial_Bases
    Imported_Marabou_Example_Linear_Unsat Imported_Marabou_Example_Relu_Sat
begin

text \<open>
  The exact simplex applied to queries, including the decoding of example
  files' bytes. All computations are by code_simp; no evaluation oracle is
  used. These results come from the HOL solver alone, without a Marabou run or
  certificate.
\<close>

section \<open>An example file, refuted by the HOL simplex\<close>

text \<open>
  examples/linear_unsat.mqx: x0 - x1 = 0 with x0 in [-2, 1/4] and x1 in [1/2, 2].
  The native triangular selection makes x1 basic in place of the auxiliary x2.
\<close>

lemma linear_unsat_file_solved:
  "map_option (\<lambda>Q. is_simplex_unsat (solve_query 20 (embed_query Q)))
     (decode_query Imported_Marabou_Example_Linear_Unsat.query_file) = Some True"
  "map_option (\<lambda>Q. is_simplex_unsat (solve_linear_part 20 2 (embed_query Q)))
     (decode_query Imported_Marabou_Example_Linear_Unsat.query_file) = Some True"
  "map_option (\<lambda>Q. basis_order 2 (select_initial_basis 2 (embed_query Q)))
     (decode_query Imported_Marabou_Example_Linear_Unsat.query_file) = Some [1]"
  by code_simp+

theorem linear_unsat_file_unsatisfiable_by_simplex:
  "decode_query Imported_Marabou_Example_Linear_Unsat.query_file = Some Q \<Longrightarrow>
     unsatisfiable (embed_query Q)"
  using linear_unsat_file_solved(1) solve_query_unsat by (simp add: is_simplex_unsat_iff)

section \<open>A satisfiable linear query\<close>

definition linear_sat_query :: query where
  "linear_sat_query =
     \<lparr>linear_atoms =
        [LinearEq (Linexpr 0 [(1, 0), (-1, 1)]) 0,
         LinearEq (Linexpr 0 [(1, 0), (1, 1), (-1, 2)]) 1],
      query_bounds =
        [Lower 0 (-2), Upper 0 1, Lower 1 (1 / 2), Upper 1 2, Lower 2 0, Upper 2 3],
      relu_atoms = []\<rparr>"

lemma linear_sat_query_solved:
  "(case solve_query 20 linear_sat_query of
      Simplex_Feasible v \<Rightarrow> Some (map v [0, 1, 2]) | _ \<Rightarrow> None) = Some [1 / 2, 1 / 2, 0]"
  by code_simp

theorem linear_sat_query_satisfiable: "satisfiable linear_sat_query"
proof -
  obtain v where "solve_query 20 linear_sat_query = Simplex_Feasible v"
    using linear_sat_query_solved by (cases "solve_query 20 linear_sat_query") auto
  then show ?thesis using solve_query_sat by (simp add: linear_sat_query_def)
qed

section \<open>ReLU queries\<close>

text \<open>An infeasible linear part refutes the query together with its ReLUs.\<close>

definition relu_linear_unsat_query :: query where
  "relu_linear_unsat_query =
     \<lparr>linear_atoms = [LinearEq (Linexpr 0 [(1, 0), (1, 1)]) 5],
      query_bounds = [Lower 0 (-2), Upper 0 2, Lower 1 0, Upper 1 2],
      relu_atoms = [ReLU 0 1]\<rparr>"

theorem relu_linear_unsat_query_unsatisfiable: "unsatisfiable relu_linear_unsat_query"
proof -
  have "is_simplex_unsat (solve_query 20 relu_linear_unsat_query)" by code_simp
  then show ?thesis using solve_query_unsat by (simp add: is_simplex_unsat_iff)
qed

text \<open>
  examples/relu_sat.mqx is satisfiable, but the solution of its linear part
  found here violates a ReLU, so no model is claimed. ReLU splitting is
  still outside the HOL solver.
\<close>

lemma relu_sat_file_relaxation_only:
  "map_option (\<lambda>Q. case solve_query 30 (embed_query Q) of
       Simplex_Feasible v \<Rightarrow> list_all (satisfies_relu_constraint v) (relu_atoms (embed_query Q))
     | _ \<Rightarrow> True)
     (decode_query Imported_Marabou_Example_Relu_Sat.query_file) = Some False"
  by code_simp

section \<open>The native initial basis\<close>

text \<open>
  Imported_Marabou_Initial_Bases proves that the selection reproduces the native
  orders of 20 captured runs. The check is not vacuous: exchanging the first two
  basic positions of the relu_split run gives an order the selection does not
  produce.
\<close>

lemma relu_split_swapped_basis_rejected:
  "map_option (\<lambda>(S, bs, ns). (bs, ns))
     (native_initial_tableau 9 (embed_query solver_relu_split_source)) \<noteq>
   Some ([6, 0, 5, 8, 7], [1, 2, 3, 4, 9, 10, 11, 12, 13])"
  unfolding solver_relu_split_native_initial_basis by simp

section \<open>Inputs the solver refuses or refutes without simplex\<close>

definition inequality_query :: query where
  "inequality_query =
     \<lparr>linear_atoms = [LinearLe (Linexpr 0 [(1, 0)]) 1],
      query_bounds = [Lower 0 0, Upper 0 2], relu_atoms = []\<rparr>"

definition unbounded_query :: query where
  "unbounded_query =
     \<lparr>linear_atoms = [LinearEq (Linexpr 0 [(1, 0), (1, 1)]) 1],
      query_bounds = [Lower 0 0, Upper 0 2, Lower 1 0], relu_atoms = []\<rparr>"

definition crossed_bounds_query :: query where
  "crossed_bounds_query =
     \<lparr>linear_atoms = [LinearEq (Linexpr 0 [(1, 0)]) 1],
      query_bounds = [Lower 0 2, Upper 0 3, Upper 0 1], relu_atoms = []\<rparr>"

lemma solver_boundaries:
  "is_simplex_unknown (solve_query 20 inequality_query)"
  "is_simplex_unknown (solve_query 20 unbounded_query)"
  "is_simplex_unsat (solve_query 20 crossed_bounds_query)"
  by code_simp+

theorem crossed_bounds_query_unsatisfiable: "unsatisfiable crossed_bounds_query"
  using solver_boundaries(3) solve_query_unsat by (simp add: is_simplex_unsat_iff)

end
