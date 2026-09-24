theory Exact_Query_Format
  imports Rational_Linear_Constraints
begin

text \<open>
  A narrow exact text format for linear/ReLU queries. Its meaning is this
  HOL decoder, so a theorem about decode_query bs is a theorem about the
  bytes bs; no external parser is trusted for that step. A file is a list of
  byte values. Grammar (SP = byte 32, LF = byte 10, exactly one SP between
  tokens, every line terminated by LF, no empty lines):

    file      = "marabou-exact-query-v1" LF (statement LF)*
    statement = kind (SP num SP var)* SP rel SP num     kind/rel: eq/=, le/<=, ge/>=
              | ("lower" | "upper") SP var SP num
              | "relu" SP var SP var                     (input, then output)
    var       = "x" digits
    num       = ["-"] digits [ "/" digits | "." digits ]

  digits are one or more ASCII 0-9. A number denotes an exact rational:
  n, n/d with d > 0, or i + f/10^(number of fraction digits); "-" negates.
  Linear statements have constant 0; statement kinds may be interleaved, and
  the query keeps each kind's order. Any other byte sequence is rejected.
\<close>

type_synonym bytes = "nat list"

definition ascii :: "string \<Rightarrow> bytes" where
  "ascii s = map of_char s"

text \<open>Byte values of the keywords, also used to evaluate the decoder.\<close>

lemma keyword_bytes [simp, code_unfold]:
  "ascii ''eq'' = [101, 113]" "ascii ''le'' = [108, 101]" "ascii ''ge'' = [103, 101]"
  "ascii ''='' = [61]" "ascii ''<='' = [60, 61]" "ascii ''>='' = [62, 61]"
  "ascii ''lower'' = [108, 111, 119, 101, 114]" "ascii ''upper'' = [117, 112, 112, 101, 114]"
  "ascii ''relu'' = [114, 101, 108, 117]"
  "ascii ''marabou-exact-query-v1'' =
     [109, 97, 114, 97, 98, 111, 117, 45, 101, 120, 97, 99, 116, 45,
      113, 117, 101, 114, 121, 45, 118, 49]"
  by (simp_all add: ascii_def)

fun split_on :: "nat \<Rightarrow> bytes \<Rightarrow> bytes list" where
  "split_on s [] = [[]]"
| "split_on s (c # cs) =
     (let r = split_on s cs in if c = s then [] # r else (c # hd r) # tl r)"

fun digits_value :: "nat \<Rightarrow> bytes \<Rightarrow> nat option" where
  "digits_value acc [] = Some acc"
| "digits_value acc (c # cs) =
     (if 48 \<le> c \<and> c \<le> 57 then digits_value (10 * acc + (c - 48)) cs else None)"

definition parse_nat :: "bytes \<Rightarrow> nat option" where
  "parse_nat cs = (if cs = [] then None else digits_value 0 cs)"

definition parse_unsigned :: "bytes \<Rightarrow> rat option" where
  "parse_unsigned cs =
    (case split_on 47 cs of
       [n, d] \<Rightarrow>
         (case (parse_nat n, parse_nat d) of
            (Some a, Some b) \<Rightarrow> if b = 0 then None else Some (of_nat a / of_nat b)
          | _ \<Rightarrow> None)
     | [w] \<Rightarrow>
         (case split_on 46 w of
            [i] \<Rightarrow> map_option of_nat (parse_nat i)
          | [i, f] \<Rightarrow>
              (case (parse_nat i, parse_nat f) of
                 (Some a, Some b) \<Rightarrow> Some (of_nat a + of_nat b / 10 ^ length f)
               | _ \<Rightarrow> None)
          | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

definition parse_rat :: "bytes \<Rightarrow> rat option" where
  "parse_rat cs =
    (if cs \<noteq> [] \<and> hd cs = 45 then map_option uminus (parse_unsigned (tl cs))
     else parse_unsigned cs)"

definition parse_var :: "bytes \<Rightarrow> var option" where
  "parse_var cs = (if cs \<noteq> [] \<and> hd cs = 120 then parse_nat (tl cs) else None)"

fun parse_pairs :: "bytes list \<Rightarrow> (rat \<times> var) list option" where
  "parse_pairs [] = Some []"
| "parse_pairs [a] = None"
| "parse_pairs (a # x # rest) =
     (case (parse_rat a, parse_var x, parse_pairs rest) of
        (Some q, Some v, Some ts) \<Rightarrow> Some ((q, v) # ts)
      | _ \<Rightarrow> None)"

datatype statement =
    Linear_Statement rat_linear_constraint
  | Bound_Statement rat_bound
  | Relu_Statement relu_constraint

definition parse_linear ::
  "bytes \<Rightarrow> (rat_linexpr \<Rightarrow> rat \<Rightarrow> rat_linear_constraint) \<Rightarrow> bytes list \<Rightarrow> statement option" where
  "parse_linear rel mk args =
    (if length args < 2 \<or> args ! (length args - 2) \<noteq> rel then None
     else case (parse_pairs (take (length args - 2) args), parse_rat (last args)) of
       (Some ts, Some b) \<Rightarrow> Some (Linear_Statement (mk (RatExpr 0 ts) b))
     | _ \<Rightarrow> None)"

definition parse_statement :: "bytes list \<Rightarrow> statement option" where
  "parse_statement toks =
    (case toks of
       [] \<Rightarrow> None
     | kw # args \<Rightarrow>
         if kw = ascii ''eq'' then parse_linear (ascii ''='') RatEq args
         else if kw = ascii ''le'' then parse_linear (ascii ''<='') RatLe args
         else if kw = ascii ''ge'' then parse_linear (ascii ''>='') RatGe args
         else if kw = ascii ''lower'' \<or> kw = ascii ''upper'' then
           (case args of
              [x, n] \<Rightarrow>
                (case (parse_var x, parse_rat n) of
                   (Some v, Some q) \<Rightarrow>
                     Some (Bound_Statement (if kw = ascii ''lower'' then RatLower v q else RatUpper v q))
                 | _ \<Rightarrow> None)
            | _ \<Rightarrow> None)
         else if kw = ascii ''relu'' then
           (case args of
              [x, y] \<Rightarrow>
                (case (parse_var x, parse_var y) of
                   (Some a, Some b) \<Rightarrow> Some (Relu_Statement (ReLU a b))
                 | _ \<Rightarrow> None)
            | _ \<Rightarrow> None)
         else None)"

definition parse_line :: "bytes \<Rightarrow> statement option" where
  "parse_line line =
    (let toks = split_on 32 line in if [] \<in> set toks then None else parse_statement toks)"

definition assemble :: "statement list \<Rightarrow> rat_query" where
  "assemble ss = \<lparr>
     rat_linear_atoms = [c. Linear_Statement c \<leftarrow> ss],
     rat_query_bounds = [b. Bound_Statement b \<leftarrow> ss],
     rat_relu_atoms = [r. Relu_Statement r \<leftarrow> ss]\<rparr>"

definition exact_query_header :: bytes where
  "exact_query_header = ascii ''marabou-exact-query-v1''"

definition decode_query :: "bytes \<Rightarrow> rat_query option" where
  "decode_query bs =
    (case split_on 10 bs of
       [] \<Rightarrow> None
     | header # rest \<Rightarrow>
         if header \<noteq> exact_query_header \<or> rest = [] \<or> last rest \<noteq> [] then None
         else map_option assemble (those (map parse_line (butlast rest))))"

text \<open>
  A build-time check, not a proof step: fail unless the byte list defined by a
  theorem c = [...] is exactly the content of a file, given relative to the
  theory directory. Generated theories also declare such files with
  external_file, so a changed file triggers rebuilding and rechecking.
\<close>

ML \<open>
structure Exact_Query_Text =
struct
  fun check_file thy thm relative =
    let
      val path = Path.append (Resources.master_directory thy) (Path.explode relative)
      val file = map Char.ord (String.explode (File.read path))
      val prop = Thm.prop_of thm
      val rhs =
        (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop) prop of
          SOME (_, r) => r
        | NONE => snd (Logic.dest_equals prop))
      val literal = map (snd o HOLogic.dest_number) (HOLogic.dest_list rhs)
    in
      if literal = file then ()
      else error ("Byte list differs from file " ^ relative)
    end
end
\<close>

text \<open>
  A file may list its statements in any order and repeat them; the query's
  meaning depends only on the three constraint sets. This lets a theorem about
  a captured query transfer to the query decoded from a differently ordered file.
\<close>

definition same_constraints :: "rat_query \<Rightarrow> rat_query \<Rightarrow> bool" where
  "same_constraints P Q \<longleftrightarrow>
     set (rat_linear_atoms P) = set (rat_linear_atoms Q) \<and>
     set (rat_query_bounds P) = set (rat_query_bounds Q) \<and>
     set (rat_relu_atoms P) = set (rat_relu_atoms Q)"

lemma same_constraints_models:
  "same_constraints P Q \<Longrightarrow>
    satisfies_query v (embed_query P) \<longleftrightarrow> satisfies_query v (embed_query Q)"
  by (simp add: same_constraints_def satisfies_query_def embed_query_def)

corollary same_constraints_unsatisfiable:
  "same_constraints P Q \<Longrightarrow> unsatisfiable (embed_query P) \<longleftrightarrow> unsatisfiable (embed_query Q)"
  using same_constraints_models unfolding unsatisfiable_def satisfiable_def by blast

definition decodes_like :: "bytes \<Rightarrow> rat_query \<Rightarrow> bool" where
  "decodes_like bs Q \<longleftrightarrow>
     (case decode_query bs of None \<Rightarrow> False | Some P \<Rightarrow> same_constraints P Q)"

lemma decodes_like_unsatisfiable:
  assumes "decodes_like bs Q" and "unsatisfiable (embed_query Q)"
      and "decode_query bs = Some P"
  shows "unsatisfiable (embed_query P)"
  using assms same_constraints_unsatisfiable by (simp add: decodes_like_def)

lemma decodes_like_model:
  assumes "decodes_like bs Q" and "satisfies_query v (embed_query Q)"
      and "decode_query bs = Some P"
  shows "satisfies_query v (embed_query P)"
  using assms same_constraints_models by (simp add: decodes_like_def)

lemma decodes_like_decodes: "decodes_like bs Q \<Longrightarrow> \<exists>P. decode_query bs = Some P"
  by (auto simp: decodes_like_def split: option.splits)

section \<open>Canonical encoder\<close>

fun print_nat :: "nat \<Rightarrow> bytes" where
  "print_nat n = (if n < 10 then [48 + n] else print_nat (n div 10) @ [48 + n mod 10])"

definition print_int :: "int \<Rightarrow> bytes" where
  "print_int i = (if i < 0 then 45 # print_nat (nat (- i)) else print_nat (nat i))"

definition print_rat :: "rat \<Rightarrow> bytes" where
  "print_rat q =
    (case quotient_of q of
       (n, d) \<Rightarrow> if d = 1 then print_int n else print_int n @ 47 # print_nat (nat d))"

definition print_var :: "var \<Rightarrow> bytes" where
  "print_var x = 120 # print_nat x"

fun print_terms :: "(rat \<times> var) list \<Rightarrow> bytes list" where
  "print_terms [] = []"
| "print_terms ((a, x) # ts) = print_rat a # print_var x # print_terms ts"

fun encode_linear :: "rat_linear_constraint \<Rightarrow> bytes list" where
  "encode_linear (RatEq e b) = ascii ''eq'' # print_terms (rat_terms e) @ [ascii ''='', print_rat b]"
| "encode_linear (RatLe e b) = ascii ''le'' # print_terms (rat_terms e) @ [ascii ''<='', print_rat b]"
| "encode_linear (RatGe e b) = ascii ''ge'' # print_terms (rat_terms e) @ [ascii ''>='', print_rat b]"

fun encode_bound :: "rat_bound \<Rightarrow> bytes list" where
  "encode_bound (RatLower x l) = [ascii ''lower'', print_var x, print_rat l]"
| "encode_bound (RatUpper x u) = [ascii ''upper'', print_var x, print_rat u]"

fun encode_relu :: "relu_constraint \<Rightarrow> bytes list" where
  "encode_relu (ReLU x y) = [ascii ''relu'', print_var x, print_var y]"

fun join :: "nat \<Rightarrow> bytes list \<Rightarrow> bytes" where
  "join s [] = []"
| "join s [w] = w"
| "join s (w # v # ws) = w @ s # join s (v # ws)"

definition encode_lines :: "rat_query \<Rightarrow> bytes list list" where
  "encode_lines Q =
    map encode_linear (rat_linear_atoms Q) @ map encode_bound (rat_query_bounds Q) @
    map encode_relu (rat_relu_atoms Q)"

definition encode_query :: "rat_query \<Rightarrow> bytes" where
  "encode_query Q =
    exact_query_header @ 10 # concat (map (\<lambda>toks. join 32 toks @ [10]) (encode_lines Q))"

section \<open>Round trip\<close>

lemma split_on_no_separator:
  "s \<notin> set xs \<Longrightarrow> split_on s xs = [xs]"
  by (induction xs) (auto simp: Let_def)

lemma split_on_append_separator:
  "s \<notin> set xs \<Longrightarrow> split_on s (xs @ s # ys) = xs # split_on s ys"
proof (induction xs)
  case Nil
  then show ?case by (simp add: Let_def)
next
  case (Cons c cs)
  then show ?case by (simp add: Let_def)
qed

lemma split_on_join:
  assumes "ws \<noteq> []" and "\<forall>w \<in> set ws. s \<notin> set w"
  shows "split_on s (join s ws) = ws"
  using assms
proof (induction s ws rule: join.induct)
  case (1 s)
  then show ?case by simp
next
  case (2 s w)
  then show ?case by (simp add: split_on_no_separator)
next
  case (3 s w v ws)
  then show ?case by (simp add: split_on_append_separator)
qed

lemma split_on_lines:
  assumes "\<forall>l \<in> set ls. s \<notin> set l"
  shows "split_on s (concat (map (\<lambda>l. l @ [s]) ls)) = ls @ [[]]"
  using assms
proof (induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons l ls)
  then show ?case
    using split_on_append_separator[of s l "concat (map (\<lambda>l. l @ [s]) ls)"] by simp
qed

declare print_nat.simps [simp del]

lemma print_nat_unfold:
  "print_nat n = (if n < 10 then [48 + n] else print_nat (n div 10) @ [48 + n mod 10])"
  by (rule print_nat.simps)

lemma digits_value_append:
  "digits_value acc (xs @ ys) =
    (case digits_value acc xs of None \<Rightarrow> None | Some a \<Rightarrow> digits_value a ys)"
  by (induction acc xs rule: digits_value.induct) auto

lemma print_nat_digits: "c \<in> set (print_nat n) \<Longrightarrow> 48 \<le> c \<and> c \<le> 57"
proof (induction n rule: print_nat.induct)
  case (1 n)
  then show ?case
    by (cases "n < 10") (auto simp: print_nat_unfold[of n])
qed

lemma print_nat_nonempty [simp]: "print_nat n \<noteq> []"
  by (subst print_nat_unfold) simp

lemma digits_value_print_nat:
  "digits_value acc (print_nat n) = Some (acc * 10 ^ length (print_nat n) + n)"
proof (induction n arbitrary: acc rule: print_nat.induct)
  case (1 n)
  show ?case
  proof (cases "n < 10")
    case True
    then show ?thesis by (simp add: print_nat_unfold[of n])
  next
    case False
    let ?k = "length (print_nat (n div 10))"
    have "digits_value acc (print_nat n) =
        digits_value (acc * 10 ^ ?k + n div 10) [48 + n mod 10]"
      using False 1 by (simp add: digits_value_append print_nat_unfold[of n])
    also have "\<dots> = Some (10 * (acc * 10 ^ ?k + n div 10) + n mod 10)"
      by simp
    also have "10 * (acc * 10 ^ ?k + n div 10) + n mod 10 = acc * 10 ^ Suc ?k + n"
      by (simp add: algebra_simps)
    finally show ?thesis
      using False by (simp add: print_nat_unfold[of n])
  qed
qed

lemma parse_nat_print_nat [simp]: "parse_nat (print_nat n) = Some n"
  by (simp add: parse_nat_def digits_value_print_nat)

lemma print_nat_not [simp]:
  "10 \<notin> set (print_nat n)" "32 \<notin> set (print_nat n)" "45 \<notin> set (print_nat n)"
  "46 \<notin> set (print_nat n)" "47 \<notin> set (print_nat n)"
  using print_nat_digits[of _ n] by fastforce+

lemma hd_print_nat_not_minus [simp]: "hd (print_nat n) \<noteq> 45"
  using print_nat_not(3)[of n] hd_in_set[OF print_nat_nonempty] by metis

lemma parse_unsigned_print_nat [simp]:
  "parse_unsigned (print_nat n) = Some (of_nat n)"
  by (simp add: parse_unsigned_def split_on_no_separator)

lemma parse_unsigned_fraction:
  assumes "0 < d"
  shows "parse_unsigned (print_nat n @ 47 # print_nat d) = Some (of_nat n / of_nat d)"
  using assms
  by (simp add: parse_unsigned_def split_on_append_separator split_on_no_separator)

lemma parse_rat_print_rat [simp]: "parse_rat (print_rat q) = Some q"
proof -
  obtain n d where quotient: "quotient_of q = (n, d)" by (cases "quotient_of q")
  have d_pos: "0 < d" by (rule quotient_of_denom_pos[OF quotient])
  have q_eq: "q = of_int n / of_int d" by (rule quotient_of_div[OF quotient])
  have printed: "print_rat q =
      (if d = 1 then print_int n else print_int n @ 47 # print_nat (nat d))"
    by (simp add: print_rat_def quotient)
  have nat_d: "0 < nat d" using d_pos by simp
  have "parse_rat (print_rat q) = Some (of_int n / of_int d)"
  proof (cases "n < 0")
    case True
    have minus: "of_nat (nat (- n)) = (- of_int n :: rat)" using True by simp
    show ?thesis
      using True nat_d d_pos
      by (auto simp: printed print_int_def parse_rat_def parse_unsigned_fraction minus)
  next
    case False
    have plain: "of_nat (nat n) = (of_int n :: rat)" using False by simp
    have "hd (print_nat (nat n) @ 47 # print_nat (nat d)) \<noteq> 45" by simp
    then show ?thesis
      using False nat_d d_pos
      by (auto simp: printed print_int_def parse_rat_def parse_unsigned_fraction plain)
  qed
  then show ?thesis by (simp only: q_eq[symmetric])
qed

lemma parse_var_print_var [simp]: "parse_var (print_var x) = Some x"
  by (simp add: parse_var_def print_var_def)

lemma parse_pairs_print_terms [simp]: "parse_pairs (print_terms ts) = Some ts"
  by (induction ts rule: print_terms.induct) simp_all

lemma print_rat_bytes:
  "c \<in> set (print_rat q) \<Longrightarrow> c = 45 \<or> c = 47 \<or> (48 \<le> c \<and> c \<le> 57)"
  using print_nat_digits
  by (fastforce simp: print_rat_def print_int_def split: prod.splits if_splits)

lemma print_rat_nonempty [simp]: "print_rat q \<noteq> []"
  by (auto simp: print_rat_def print_int_def split: prod.splits)

definition good_token :: "bytes \<Rightarrow> bool" where
  "good_token w \<longleftrightarrow> w \<noteq> [] \<and> 32 \<notin> set w \<and> 10 \<notin> set w"

lemma good_print_rat [simp]: "good_token (print_rat q)"
  using print_rat_bytes[of 32 q] print_rat_bytes[of 10 q] by (auto simp: good_token_def)

lemma good_print_var [simp]: "good_token (print_var x)"
  by (simp add: good_token_def print_var_def)

lemma good_print_terms: "w \<in> set (print_terms ts) \<Longrightarrow> good_token w"
  by (induction ts rule: print_terms.induct) auto

fun linear_constant :: "rat_linear_constraint \<Rightarrow> rat" where
  "linear_constant (RatEq e b) = rat_constant e"
| "linear_constant (RatLe e b) = rat_constant e"
| "linear_constant (RatGe e b) = rat_constant e"

definition encodable_query :: "rat_query \<Rightarrow> bool" where
  "encodable_query Q \<longleftrightarrow> (\<forall>c \<in> set (rat_linear_atoms Q). linear_constant c = 0)"

fun encode_statement :: "statement \<Rightarrow> bytes list" where
  "encode_statement (Linear_Statement c) = encode_linear c"
| "encode_statement (Bound_Statement b) = encode_bound b"
| "encode_statement (Relu_Statement r) = encode_relu r"

fun encodable_statement :: "statement \<Rightarrow> bool" where
  "encodable_statement (Linear_Statement c) = (linear_constant c = 0)"
| "encodable_statement _ = True"

lemma encode_linear_good: "w \<in> set (encode_linear c) \<Longrightarrow> good_token w"
  by (cases c) (auto simp: good_print_terms, simp_all add: good_token_def)

lemma encode_bound_good: "w \<in> set (encode_bound b) \<Longrightarrow> good_token w"
  by (cases b) (auto simp: good_token_def print_var_def dest: print_rat_bytes)

lemma encode_relu_good: "w \<in> set (encode_relu r) \<Longrightarrow> good_token w"
  by (cases r) (auto simp: good_token_def print_var_def)

lemma encode_statement_good:
  "w \<in> set (encode_statement st) \<Longrightarrow> good_token w"
  by (cases st) (auto intro: encode_linear_good encode_bound_good encode_relu_good)

lemma encode_statement_nonempty: "encode_statement st \<noteq> []"
  by (cases st rule: encode_statement.cases)
     (auto elim!: encode_linear.elims encode_bound.elims encode_relu.elims)

lemma parse_linear_encoded:
  "parse_linear rel mk (print_terms ts @ [rel, print_rat b]) =
    Some (Linear_Statement (mk (RatExpr 0 ts) b))"
  by (simp add: parse_linear_def nth_append)

lemma rat_expr_zero_constant: "rat_constant e = 0 \<Longrightarrow> RatExpr 0 (rat_terms e) = e"
  by (cases e) simp

lemma parse_statement_encode:
  assumes "encodable_statement st"
  shows "parse_statement (encode_statement st) = Some st"
proof (cases st)
  case (Linear_Statement c)
  then show ?thesis
    using assms
    by (cases c) (simp_all add: parse_statement_def parse_linear_encoded rat_expr_zero_constant)
next
  case (Bound_Statement b)
  then show ?thesis by (cases b) (simp_all add: parse_statement_def)
next
  case (Relu_Statement r)
  then show ?thesis by (cases r) (simp add: parse_statement_def)
qed

lemma join_bytes: "c \<in> set (join s ws) \<Longrightarrow> c = s \<or> (\<exists>w \<in> set ws. c \<in> set w)"
  by (induction s ws rule: join.induct) auto

lemma parse_line_encode:
  assumes "encodable_statement st"
  shows "parse_line (join 32 (encode_statement st)) = Some st"
proof -
  have tokens: "\<forall>w \<in> set (encode_statement st). 32 \<notin> set w \<and> w \<noteq> []"
    using encode_statement_good by (auto simp: good_token_def)
  have "split_on 32 (join 32 (encode_statement st)) = encode_statement st"
    using tokens encode_statement_nonempty by (auto intro: split_on_join)
  moreover have "[] \<notin> set (encode_statement st)" using tokens by auto
  ultimately show ?thesis
    using parse_statement_encode[OF assms] by (simp add: parse_line_def)
qed

lemma encoded_line_no_newline: "10 \<notin> set (join 32 (encode_statement st))"
  using join_bytes[of 10 32 "encode_statement st"] encode_statement_good
  by (auto simp: good_token_def)

lemma those_map_Some:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x = Some x) \<Longrightarrow> those (map f xs) = Some xs"
  by (induction xs) auto

definition query_statements :: "rat_query \<Rightarrow> statement list" where
  "query_statements Q =
    map Linear_Statement (rat_linear_atoms Q) @ map Bound_Statement (rat_query_bounds Q) @
    map Relu_Statement (rat_relu_atoms Q)"

lemma encode_lines_statements:
  "encode_lines Q = map encode_statement (query_statements Q)"
  by (simp add: encode_lines_def query_statements_def)

lemma concat_map_nil [simp]: "concat (map (\<lambda>x. []) xs) = []"
  by (induction xs) simp_all

lemma concat_map_single [simp]: "concat (map (\<lambda>x. [x]) xs) = xs"
  by (induction xs) simp_all

lemma assemble_query_statements:
  "assemble (query_statements (Q :: rat_query)) = Q"
  by (cases Q) (simp add: assemble_def query_statements_def comp_def)

lemma header_no_newline: "10 \<notin> set exact_query_header"
  by (simp add: exact_query_header_def ascii_def)

theorem decode_encode_query:
  assumes "encodable_query Q"
  shows "decode_query (encode_query Q) = Some Q"
proof -
  let ?lines = "map (join 32 \<circ> encode_statement) (query_statements Q)"
  have statements: "\<And>st. st \<in> set (query_statements Q) \<Longrightarrow> encodable_statement st"
    using assms by (auto simp: query_statements_def encodable_query_def)
  have lines_ok: "\<forall>l \<in> set ?lines. 10 \<notin> set l"
    using encoded_line_no_newline by auto
  have split: "split_on 10 (encode_query Q) = exact_query_header # ?lines @ [[]]"
    using split_on_append_separator[OF header_no_newline] split_on_lines[OF lines_ok]
    by (simp add: encode_query_def encode_lines_statements comp_def)
  have "those (map parse_line ?lines) =
      those (map (\<lambda>st. parse_line (join 32 (encode_statement st))) (query_statements Q))"
    by (simp add: comp_def)
  also have "\<dots> = Some (query_statements Q)"
    by (rule those_map_Some) (simp add: parse_line_encode statements)
  finally have parsed: "those (map parse_line ?lines) = Some (query_statements Q)" .
  show ?thesis
    using parsed by (simp add: decode_query_def split assemble_query_statements)
qed

end
