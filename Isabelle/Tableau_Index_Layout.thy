theory Tableau_Index_Layout
  imports Tableau_Simplex_Step
begin

text \<open>
  The index maps and value arrays of src/engine/Tableau.h:
  _basicIndexToVariable, _nonBasicIndexToVariable, _variableToIndex,
  _basicAssignment and _nonBasicAssignment. A pivot swaps one position of
  each index map (Tableau.cpp:779-782, 828-831); performDegeneratePivot then
  swaps the two array entries (839-841), whereas performPivot has already
  written the new values into the old positions in updateAssignmentForPivot
  (2406-2456). This theory proves that both array operations implement the
  variable-indexed exchange of Tableau_Pivot. Arrays are exact lists; no
  memory, bounds checking or floating point is modeled.
\<close>

record tableau_layout =
  basic_index :: "var list"
  nonbasic_index :: "var list"
  basic_assignment :: "real list"
  nonbasic_assignment :: "real list"

fun position :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "position [] x = 0"
| "position (y # ys) x = (if y = x then 0 else Suc (position ys x))"

lemma position_less: "x \<in> set xs \<Longrightarrow> position xs x < length xs"
  by (induction xs) auto

lemma nth_position [simp]: "x \<in> set xs \<Longrightarrow> xs ! position xs x = x"
  by (induction xs) auto

lemma position_nth [simp]: "distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> position xs (xs ! i) = i"
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (cases i) (auto simp: nth_mem)
qed

definition layout_valid :: "tableau_layout \<Rightarrow> bool" where
  "layout_valid L \<longleftrightarrow>
     distinct (basic_index L @ nonbasic_index L) \<and>
     length (basic_assignment L) = length (basic_index L) \<and>
     length (nonbasic_assignment L) = length (nonbasic_index L)"

text \<open>_variableToIndex: a variable's position in whichever index map holds it.\<close>

definition variable_to_index :: "tableau_layout \<Rightarrow> var \<Rightarrow> nat" where
  "variable_to_index L x =
     (if x \<in> set (basic_index L) then position (basic_index L) x
      else position (nonbasic_index L) x)"

definition layout_abstracts :: "tableau_layout \<Rightarrow> tableau_state \<Rightarrow> bool" where
  "layout_abstracts L S \<longleftrightarrow>
     layout_valid L \<and>
     tableau_basics S = set (basic_index L) \<and>
     tableau_nonbasics S = set (nonbasic_index L) \<and>
     (\<forall>i<length (basic_index L).
        tableau_basic_value S (basic_index L ! i) = basic_assignment L ! i) \<and>
     (\<forall>k<length (nonbasic_index L).
        tableau_nonbasic_value S (nonbasic_index L ! k) = nonbasic_assignment L ! k)"

text \<open>
  The change column d = B\<inverse> A_e (computeChangeColumn, 1452-1457) in the
  row representation: row coefficients are -d.
\<close>

definition change_column :: "tableau_state \<Rightarrow> var \<Rightarrow> var list \<Rightarrow> real list" where
  "change_column S e bs = map (\<lambda>x. - row_coefficient (tableau_rows S x) e) bs"

section \<open>The native operations\<close>

definition swap_indices :: "tableau_layout \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tableau_layout" where
  "swap_indices L l k = L\<lparr>
     basic_index := (basic_index L)[l := nonbasic_index L ! k],
     nonbasic_index := (nonbasic_index L)[k := basic_index L ! l]\<rparr>"

definition native_degenerate_pivot :: "tableau_layout \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tableau_layout" where
  "native_degenerate_pivot L l k =
     (swap_indices L l k)\<lparr>
        basic_assignment := (basic_assignment L)[l := nonbasic_assignment L ! k],
        nonbasic_assignment := (nonbasic_assignment L)[k := basic_assignment L ! l]\<rparr>"

text \<open>
  updateAssignmentForPivot for a real pivot: every other basic moves by
  -d_i * delta, the leaving slot receives the entering variable's new value and
  the entering slot receives the leaving variable's target; then the index
  maps are swapped.
\<close>

definition native_pivot ::
  "tableau_layout \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> tableau_layout" where
  "native_pivot L l k d delta target =
     (swap_indices L l k)\<lparr>
        basic_assignment :=
          map (\<lambda>i. if i = l then nonbasic_assignment L ! k + delta
                    else basic_assignment L ! i - d ! i * delta)
            [0..<length (basic_index L)],
        nonbasic_assignment := (nonbasic_assignment L)[k := target]\<rparr>"

text \<open>A bound flip ("fake pivot", 2375-2404) moves the basics and the entering value only.\<close>

definition native_bound_flip ::
  "tableau_layout \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> tableau_layout" where
  "native_bound_flip L k d delta =
     L\<lparr>basic_assignment :=
          map (\<lambda>i. basic_assignment L ! i - d ! i * delta) [0..<length (basic_index L)],
        nonbasic_assignment :=
          (nonbasic_assignment L)[k := nonbasic_assignment L ! k + delta]\<rparr>"

section \<open>Index-map facts\<close>

lemma layout_swap_valid:
  assumes "layout_valid L" "l < length (basic_index L)" "k < length (nonbasic_index L)"
  shows "distinct ((basic_index L)[l := nonbasic_index L ! k] @
                   (nonbasic_index L)[k := basic_index L ! l])"
proof -
  let ?B = "basic_index L" and ?N = "nonbasic_index L"
  have d: "distinct ?B" "distinct ?N" "set ?B \<inter> set ?N = {}"
    using assms(1) unfolding layout_valid_def by auto
  have e: "?N ! k \<notin> set ?B" and b: "?B ! l \<notin> set ?N"
    using d assms(2,3) nth_mem by blast+
  have dB: "distinct (?B[l := ?N ! k])"
    using d(1) e assms(2) by (simp add: distinct_list_update set_update_distinct)
  have dN: "distinct (?N[k := ?B ! l])"
    using d(2) b assms(3) by (simp add: distinct_list_update set_update_distinct)
  have sB: "set (?B[l := ?N ! k]) = insert (?N ! k) (set ?B - {?B ! l})"
    using d(1) assms(2) by (simp add: set_update_distinct)
  have sN: "set (?N[k := ?B ! l]) = insert (?B ! l) (set ?N - {?N ! k})"
    using d(2) assms(3) by (simp add: set_update_distinct)
  have mem: "?B ! l \<in> set ?B" "?N ! k \<in> set ?N"
    using assms(2,3) by simp_all
  have "set (?B[l := ?N ! k]) \<inter> set (?N[k := ?B ! l]) = {}"
    unfolding sB sN using d(3) e b mem by auto
  then show ?thesis using dB dN by simp
qed

lemma variable_to_index_after_swap:
  assumes valid: "layout_valid L" and l: "l < length (basic_index L)"
      and k: "k < length (nonbasic_index L)"
  defines "L' \<equiv> swap_indices L l k"
  shows "variable_to_index L' (basic_index L ! l) = k"
    and "variable_to_index L' (nonbasic_index L ! k) = l"
    and "x \<noteq> basic_index L ! l \<Longrightarrow> x \<noteq> nonbasic_index L ! k \<Longrightarrow>
         x \<in> set (basic_index L) \<union> set (nonbasic_index L) \<Longrightarrow>
         variable_to_index L' x = variable_to_index L x"
proof -
  let ?B = "basic_index L" and ?N = "nonbasic_index L"
  have d: "distinct ?B" "distinct ?N" "set ?B \<inter> set ?N = {}"
    using valid unfolding layout_valid_def by auto
  have dist: "distinct (?B[l := ?N ! k] @ ?N[k := ?B ! l])"
    using layout_swap_valid[OF valid l k] .
  have len: "length (?B[l := ?N ! k]) = length ?B" "length (?N[k := ?B ! l]) = length ?N"
    by simp_all
  have bN: "?B ! l \<in> set (?N[k := ?B ! l])" using k by (simp add: set_update_memI)
  have bB: "?B ! l \<notin> set (?B[l := ?N ! k])" using dist bN by auto
  have eB: "?N ! k \<in> set (?B[l := ?N ! k])" using l by (simp add: set_update_memI)
  show "variable_to_index L' (?B ! l) = k"
    using bB dist k position_nth[of "?N[k := ?B ! l]" k]
    by (simp add: L'_def swap_indices_def variable_to_index_def)
  show "variable_to_index L' (?N ! k) = l"
    using eB dist l position_nth[of "?B[l := ?N ! k]" l]
    by (simp add: L'_def swap_indices_def variable_to_index_def)
  assume xb: "x \<noteq> ?B ! l" and xe: "x \<noteq> ?N ! k" and x: "x \<in> set ?B \<union> set ?N"
  show "variable_to_index L' x = variable_to_index L x"
  proof (cases "x \<in> set ?B")
    case True
    obtain i where i: "i < length ?B" "?B ! i = x" using True by (auto simp: in_set_conv_nth)
    have il: "i \<noteq> l" using i xb by auto
    have "?B[l := ?N ! k] ! i = x" using i il by simp
    moreover have "x \<in> set (?B[l := ?N ! k])"
      using i il by (metis length_list_update nth_mem calculation)
    ultimately show ?thesis
      using True i dist d(1) position_nth[of "?B[l := ?N ! k]" i] position_nth[of ?B i]
      by (simp add: L'_def swap_indices_def variable_to_index_def)
  next
    case False
    then have xN: "x \<in> set ?N" using x by blast
    obtain i where i: "i < length ?N" "?N ! i = x" using xN by (auto simp: in_set_conv_nth)
    have ik: "i \<noteq> k" using i xe by auto
    have x_new: "?N[k := ?B ! l] ! i = x" using i ik by simp
    have notB: "x \<notin> set (?B[l := ?N ! k])"
    proof
      assume "x \<in> set (?B[l := ?N ! k])"
      moreover have "x \<in> set (?N[k := ?B ! l])"
        using i x_new by (metis length_list_update nth_mem)
      ultimately show False using dist by auto
    qed
    show ?thesis
      using False notB i x_new dist d(2) position_nth[of "?N[k := ?B ! l]" i] position_nth[of ?N i]
      by (simp add: L'_def swap_indices_def variable_to_index_def)
  qed
qed

section \<open>Refinement of the exchange\<close>

lemma exchange_values:
  "tableau_basic_value (exchange_basis S b e) = (tableau_basic_value S)(e := tableau_nonbasic_value S e)"
  "tableau_nonbasic_value (exchange_basis S b e) = (tableau_nonbasic_value S)(b := tableau_basic_value S b)"
  by (simp_all add: exchange_basis_def)

lemma layout_abstracts_facts:
  assumes "layout_abstracts L S" "l < length (basic_index L)" "k < length (nonbasic_index L)"
  shows "distinct (basic_index L)" "distinct (nonbasic_index L)"
    "set (basic_index L) \<inter> set (nonbasic_index L) = {}"
    "basic_index L ! l \<in> tableau_basics S" "nonbasic_index L ! k \<in> tableau_nonbasics S"
    "nonbasic_index L ! k \<notin> set (basic_index L)" "basic_index L ! l \<notin> set (nonbasic_index L)"
  using assms nth_mem unfolding layout_abstracts_def layout_valid_def by auto

theorem native_degenerate_pivot_refines:
  assumes abs: "layout_abstracts L S"
      and l: "l < length (basic_index L)" and k: "k < length (nonbasic_index L)"
  shows "layout_abstracts (native_degenerate_pivot L l k)
           (exchange_basis S (basic_index L ! l) (nonbasic_index L ! k))"
proof -
  let ?B = "basic_index L" and ?N = "nonbasic_index L"
  let ?b = "?B ! l" and ?e = "?N ! k"
  let ?L' = "native_degenerate_pivot L l k" and ?S' = "exchange_basis S ?b ?e"
  note f = layout_abstracts_facts[OF abs l k]
  have valid: "layout_valid L" using abs unfolding layout_abstracts_def by blast
  have bv: "\<And>i. i < length ?B \<Longrightarrow> tableau_basic_value S (?B ! i) = basic_assignment L ! i"
    and nv: "\<And>j. j < length ?N \<Longrightarrow> tableau_nonbasic_value S (?N ! j) = nonbasic_assignment L ! j"
    and sets: "tableau_basics S = set ?B" "tableau_nonbasics S = set ?N"
    using abs unfolding layout_abstracts_def by auto
  have lens: "length (basic_assignment L) = length ?B" "length (nonbasic_assignment L) = length ?N"
    using valid unfolding layout_valid_def by auto
  have be: "?b \<noteq> ?e" using f(6) l nth_mem by metis
  have valid': "layout_valid ?L'"
    using layout_swap_valid[OF valid l k] lens
    by (simp add: layout_valid_def native_degenerate_pivot_def swap_indices_def)
  have basics': "tableau_basics ?S' = set (basic_index ?L')"
    using f(1) l sets by (simp add: native_degenerate_pivot_def swap_indices_def set_update_distinct)
  have nonbasics': "tableau_nonbasics ?S' = set (nonbasic_index ?L')"
    using f(2) k sets by (simp add: native_degenerate_pivot_def swap_indices_def set_update_distinct)
  have basic_vals: "\<forall>i<length (basic_index ?L').
      tableau_basic_value ?S' (basic_index ?L' ! i) = basic_assignment ?L' ! i"
  proof (intro allI impI)
    fix i
    assume i: "i < length (basic_index ?L')"
    then have i': "i < length ?B" by (simp add: native_degenerate_pivot_def swap_indices_def)
    show "tableau_basic_value ?S' (basic_index ?L' ! i) = basic_assignment ?L' ! i"
    proof (cases "i = l")
      case True
      then show ?thesis
        using l k lens nv[OF k]
        by (simp add: native_degenerate_pivot_def swap_indices_def exchange_values)
    next
      case False
      have "?B ! i \<noteq> ?e" using f(6) i' nth_mem by metis
      then show ?thesis
        using False i' lens bv[OF i']
        by (simp add: native_degenerate_pivot_def swap_indices_def exchange_values)
    qed
  qed
  have nonbasic_vals: "\<forall>j<length (nonbasic_index ?L').
      tableau_nonbasic_value ?S' (nonbasic_index ?L' ! j) = nonbasic_assignment ?L' ! j"
  proof (intro allI impI)
    fix j
    assume j: "j < length (nonbasic_index ?L')"
    then have j': "j < length ?N" by (simp add: native_degenerate_pivot_def swap_indices_def)
    show "tableau_nonbasic_value ?S' (nonbasic_index ?L' ! j) = nonbasic_assignment ?L' ! j"
    proof (cases "j = k")
      case True
      then show ?thesis
        using l k lens bv[OF l]
        by (simp add: native_degenerate_pivot_def swap_indices_def exchange_values)
    next
      case False
      have "?N ! j \<noteq> ?b" using f(7) j' nth_mem by metis
      then show ?thesis
        using False j' lens nv[OF j']
        by (simp add: native_degenerate_pivot_def swap_indices_def exchange_values)
    qed
  qed
  show ?thesis
    unfolding layout_abstracts_def
    using valid' basics' nonbasics' basic_vals nonbasic_vals by blast
qed

lemma move_values_general:
  assumes "x \<in> tableau_basics S"
  shows "tableau_basic_value (update_nonbasic_assignment S e (tableau_nonbasic_value S e + delta)) x =
           tableau_basic_value S x + row_coefficient (tableau_rows S x) e * delta"
  using assms
  by (simp add: update_nonbasic_assignment_def update_coefficient_is_row_coefficient)

theorem native_pivot_refines:
  assumes abs: "layout_abstracts L S"
      and l: "l < length (basic_index L)" and k: "k < length (nonbasic_index L)"
  defines "b \<equiv> basic_index L ! l" and "e \<equiv> nonbasic_index L ! k"
  shows "layout_abstracts
           (native_pivot L l k (change_column S e (basic_index L)) delta
              (tableau_basic_value S b + row_coefficient (tableau_rows S b) e * delta))
           (exchange_basis
              (update_nonbasic_assignment S e (tableau_nonbasic_value S e + delta)) b e)"
proof -
  let ?B = "basic_index L" and ?N = "nonbasic_index L"
  let ?M = "update_nonbasic_assignment S e (tableau_nonbasic_value S e + delta)"
  let ?d = "change_column S e ?B"
  let ?t = "tableau_basic_value S b + row_coefficient (tableau_rows S b) e * delta"
  let ?L' = "native_pivot L l k ?d delta ?t" and ?S' = "exchange_basis ?M b e"
  note f = layout_abstracts_facts[OF abs l k]
  have valid: "layout_valid L" using abs unfolding layout_abstracts_def by blast
  have bv: "\<And>i. i < length ?B \<Longrightarrow> tableau_basic_value S (?B ! i) = basic_assignment L ! i"
    and nv: "\<And>j. j < length ?N \<Longrightarrow> tableau_nonbasic_value S (?N ! j) = nonbasic_assignment L ! j"
    and sets: "tableau_basics S = set ?B" "tableau_nonbasics S = set ?N"
    using abs unfolding layout_abstracts_def by auto
  have lens: "length (basic_assignment L) = length ?B" "length (nonbasic_assignment L) = length ?N"
    using valid unfolding layout_valid_def by auto
  have valid': "layout_valid ?L'"
    using layout_swap_valid[OF valid l k] lens
    by (simp add: layout_valid_def native_pivot_def swap_indices_def b_def e_def)
  have basics': "tableau_basics ?S' = set (basic_index ?L')"
    using f(1) l sets
    by (simp add: native_pivot_def swap_indices_def set_update_distinct b_def e_def)
  have nonbasics': "tableau_nonbasics ?S' = set (nonbasic_index ?L')"
    using f(2) k sets
    by (simp add: native_pivot_def swap_indices_def set_update_distinct b_def e_def)
  have e_val: "tableau_nonbasic_value S e = nonbasic_assignment L ! k"
    using nv[OF k] by (simp add: e_def)
  have basic_vals: "\<forall>i<length (basic_index ?L').
      tableau_basic_value ?S' (basic_index ?L' ! i) = basic_assignment ?L' ! i"
  proof (intro allI impI)
    fix i
    assume i: "i < length (basic_index ?L')"
    then have i': "i < length ?B" by (simp add: native_pivot_def swap_indices_def)
    show "tableau_basic_value ?S' (basic_index ?L' ! i) = basic_assignment ?L' ! i"
    proof (cases "i = l")
      case True
      then show ?thesis
        using l k e_val
        by (simp add: native_pivot_def swap_indices_def exchange_values
            update_nonbasic_assignment_def e_def)
    next
      case False
      have x: "?B ! i \<in> tableau_basics S" using i' sets nth_mem by metis
      have ne: "?B ! i \<noteq> e" using f(6) i' nth_mem unfolding e_def by metis
      have "tableau_basic_value ?S' (?B ! i) =
          basic_assignment L ! i - ?d ! i * delta"
        using ne move_values_general[OF x, of e delta] bv[OF i'] i'
        by (simp add: exchange_values change_column_def)
      then show ?thesis
        using False i' by (simp add: native_pivot_def swap_indices_def)
    qed
  qed
  have nonbasic_vals: "\<forall>j<length (nonbasic_index ?L').
      tableau_nonbasic_value ?S' (nonbasic_index ?L' ! j) = nonbasic_assignment ?L' ! j"
  proof (intro allI impI)
    fix j
    assume j: "j < length (nonbasic_index ?L')"
    then have j': "j < length ?N" by (simp add: native_pivot_def swap_indices_def)
    show "tableau_nonbasic_value ?S' (nonbasic_index ?L' ! j) = nonbasic_assignment ?L' ! j"
    proof (cases "j = k")
      case True
      have b: "b \<in> tableau_basics S" using f(4) unfolding b_def .
      then show ?thesis
        using True k lens move_values_general[OF b, of e delta]
        by (simp add: native_pivot_def swap_indices_def exchange_values b_def)
    next
      case False
      have nb: "?N ! j \<noteq> b" using f(7) j' nth_mem unfolding b_def by metis
      have ne: "?N ! j \<noteq> e" using False f(2) j' k unfolding e_def by (simp add: nth_eq_iff_index_eq)
      then show ?thesis
        using False nb j' lens nv[OF j']
        by (simp add: native_pivot_def swap_indices_def exchange_values
            update_nonbasic_assignment_def)
    qed
  qed
  show ?thesis
    unfolding layout_abstracts_def
    using valid' basics' nonbasics' basic_vals nonbasic_vals by blast
qed

theorem native_bound_flip_refines:
  assumes abs: "layout_abstracts L S" and k: "k < length (nonbasic_index L)"
  defines "e \<equiv> nonbasic_index L ! k"
  shows "layout_abstracts
           (native_bound_flip L k (change_column S e (basic_index L)) delta)
           (update_nonbasic_assignment S e (tableau_nonbasic_value S e + delta))"
proof -
  let ?B = "basic_index L" and ?N = "nonbasic_index L"
  let ?M = "update_nonbasic_assignment S e (tableau_nonbasic_value S e + delta)"
  let ?L' = "native_bound_flip L k (change_column S e ?B) delta"
  have valid: "layout_valid L" using abs unfolding layout_abstracts_def by blast
  have bv: "\<And>i. i < length ?B \<Longrightarrow> tableau_basic_value S (?B ! i) = basic_assignment L ! i"
    and nv: "\<And>j. j < length ?N \<Longrightarrow> tableau_nonbasic_value S (?N ! j) = nonbasic_assignment L ! j"
    and sets: "tableau_basics S = set ?B" "tableau_nonbasics S = set ?N"
    using abs unfolding layout_abstracts_def by auto
  have dN: "distinct ?N" using valid unfolding layout_valid_def by auto
  have lens: "length (basic_assignment L) = length ?B" "length (nonbasic_assignment L) = length ?N"
    using valid unfolding layout_valid_def by auto
  have valid': "layout_valid ?L'"
    using valid lens by (simp add: layout_valid_def native_bound_flip_def)
  have basic_vals: "\<forall>i<length ?B. tableau_basic_value ?M (?B ! i) = basic_assignment ?L' ! i"
  proof (intro allI impI)
    fix i
    assume i: "i < length ?B"
    have x: "?B ! i \<in> tableau_basics S" using i sets nth_mem by metis
    show "tableau_basic_value ?M (?B ! i) = basic_assignment ?L' ! i"
      using move_values_general[OF x, of e delta] bv[OF i] i
      by (simp add: native_bound_flip_def change_column_def)
  qed
  have nonbasic_vals: "\<forall>j<length ?N.
      tableau_nonbasic_value ?M (?N ! j) = nonbasic_assignment ?L' ! j"
  proof (intro allI impI)
    fix j
    assume j: "j < length ?N"
    show "tableau_nonbasic_value ?M (?N ! j) = nonbasic_assignment ?L' ! j"
    proof (cases "j = k")
      case True
      then show ?thesis
        using k lens nv[OF k]
        by (simp add: native_bound_flip_def update_nonbasic_assignment_def e_def)
    next
      case False
      have "?N ! j \<noteq> e" using False dN j k unfolding e_def by (simp add: nth_eq_iff_index_eq)
      then show ?thesis
        using False j lens nv[OF j]
        by (simp add: native_bound_flip_def update_nonbasic_assignment_def)
    qed
  qed
  show ?thesis
    unfolding layout_abstracts_def
    using valid' sets basic_vals nonbasic_vals
    by (simp add: native_bound_flip_def)
qed

text \<open>
  With the exact Harris choice, the native formulas of updateAssignmentForPivot
  (delta = (target - value) / pivot, the target from leaving_native_formulas)
  produce exactly the state of apply_choice.
\<close>

corollary native_simplex_pivot_refines:
  assumes abs: "layout_abstracts L S"
      and l: "l < length (basic_index L)" and k: "k < length (nonbasic_index L)"
      and ratio: "basic_ratio S (nonbasic_index L ! k) d (basic_index L ! l) = Some \<tau>"
  defines "b \<equiv> basic_index L ! l" and "e \<equiv> nonbasic_index L ! k"
  defines "target \<equiv> native_leaving_target S b (0 < step_rate S e d b)"
  shows "layout_abstracts
           (native_pivot L l k (change_column S e (basic_index L))
              ((target - tableau_basic_value S b) / row_coefficient (tableau_rows S b) e)
              target)
           (apply_choice S e d (Leaving b \<tau>))"
proof -
  have b: "b \<in> tableau_basics S" using layout_abstracts_facts(4)[OF abs l k] by (simp add: b_def)
  have r: "basic_ratio S e d b = Some \<tau>" using ratio by (simp add: b_def e_def)
  have delta: "(target - tableau_basic_value S b) / row_coefficient (tableau_rows S b) e =
      direction_sign d * \<tau>"
    using leaving_native_formulas(2)[OF r b] by (simp add: target_def)
  have t: "target = tableau_basic_value S b +
      row_coefficient (tableau_rows S b) e * (direction_sign d * \<tau>)"
    using leaving_native_formulas(1)[OF r b] move_values_general[OF b, of e "direction_sign d * \<tau>"]
    by (simp add: target_def move_entering_def)
  show ?thesis
    using native_pivot_refines[OF abs l k, of "direction_sign d * \<tau>"] delta t
    by (simp add: b_def e_def move_entering_def)
qed

end
