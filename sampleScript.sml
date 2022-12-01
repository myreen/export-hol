open HolKernel Parse boolLib bossLib arithmeticTheory integerTheory;

val _ = new_theory "sample";

(* a few sample definitions *)

Definition fib_def:
  fib (n:num) = if n < 2 then n else fib (n-1) + fib (n-2)
End

Datatype:
  rose = Tree α (rose list)
End

Definition flatten_def:
  flatten (Tree x ts) = [x] ++ FLAT (MAP flatten ts)
Termination
  WF_REL_TAC ‘measure $ rose_size $ K 0’
End

Inductive add_rel:
  (∀m:num.
    add_rel 0 m m) ∧
  (∀m n k.
    add_rel n (SUC m) k ⇒
    add_rel (SUC n) m k)
End

(* a sanity lemma *)

Theorem add_rel_thm:
  ∀m n k. add_rel m n k ⇒ k = m + n
Proof
  Induct_on ‘add_rel’ \\ rw []
QED

(* sketch of some automation *)

val term_patterns =
  [(“_m + _n:num”,"mk_add"),
   (“_m - _n:num”,"mk_sub"),
   (“_m < _n:num”,"mk_lt"),
   (“_m ≤ _n:num”,"mk_le"),
   (“_m = _n:'a”,"mk_eq"),
   (“_m ⇒ _n:bool”,"mk_imp"),
   (“SUC _m”,"mk_suc"),
   (“if _a then _b else _c”,"mk_if")];

datatype output = String of string
                | App of bool * string * output list;

fun app x y = App (false,x,y);
fun quote s = String ("\"" ^ s ^ "\"")

fun export_ty ty =
  if ty = “:bool” then String "bool_ty" else
  if ty = “:unit” then String "unit_ty" else
  if ty = “:num”  then String "nat_ty" else
  if ty = “:int”  then String "int_ty" else
  let
    val n = dest_vartype ty
  in app "mk_var_type" [quote n] end handle HOL_ERR _ =>
  let
    val (n,tys) = dest_type ty
  in app "mk_type" (quote n :: map export_ty tys)  end

fun export tm =
  let
    val (v,ty) = dest_var tm
  in app "mk_var" [quote v] end handle HOL_ERR _ =>
  let
    val (v,x) = dest_abs tm
    val (s,ty) = dest_var v
  in app "mk_lam" [quote s, export x] end handle HOL_ERR _ =>
  let
    val n = numSyntax.dest_numeral tm
  in app "mk_num" [String (Arbnum.toString n)] end handle HOL_ERR _ =>
  let
    fun match_pat (pat,s) = let
      val (i,j) = match_term pat tm
      val xs = map (fn {redex = x, residue = y} => (fst (dest_var x),y)) i
      val ys = sort (fn (x,_) => fn (y,_) => String.compare(x,y) = LESS) xs
      in (s,map snd ys) end
    fun map_fst f [] = fail()
      | map_fst f (x::xs) = f x handle HOL_ERR _ => map_fst f xs
    val (s,args) = map_fst match_pat term_patterns
  in app s (map export args) end handle HOL_ERR _ =>
  let
    val (f,x) = dest_comb tm
  in app "mk_app" [export f, export x] end handle HOL_ERR _ =>
  let
    val (n,ty) = dest_const tm
  in app "mk_const" [quote n] end;

fun print_output out =
  let
    val threshold = 80
    fun annotate (String s) = (String s, size s)
      | annotate (App (_,s,xs)) =
          let val ys = map annotate xs
              val n = foldr (fn ((_,m),n) => n+m) 0 ys + size s + 3
              val zs = map fst ys
          in (App (n < threshold, s, zs), n) end
    fun print_o indent (String s) = print s
      | print_o indent (App (b,s,xs)) =
          if b then
            (print s; print "("; print_o_list "" xs; print ")")
          else
            let val new_indent = indent ^ "  "
            in print s;
               print "(";
               print new_indent;
               print_o_list new_indent xs;
               print ")"
            end
    and print_o_list indent [] = ()
      | print_o_list indent [x] = print_o indent x
      | print_o_list indent (x::xs) =
          (print_o indent x; print (", " ^ indent); print_o_list indent xs)
  val _ = print "\n\n"
  val _ = print_o "\n" (fst (annotate out))
  val _ = print ";;\n\n"
  in () end;

val def = fib_def
val tm = def |> SPEC_ALL |> concl
val c = tm |> dest_eq |> fst |> repeat rator
val (cname,cty) = dest_const c
val out = app "define" [quote cname, export_ty cty, export tm]
val _ = print_output out

val _ = export_theory();
