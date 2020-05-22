From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssralg ssrnum ssrint.

Import GRing.
Open Scope ring_scope.

Definition IMO1_problem (f: int -> int) := forall a b: int,
    (f(a * 2%:R) + f(b) * 2%:R = f(f(a + b))).

Definition IMO1_solution (f: int -> int) :=
  (exists t : int, forall x, f(x) = (x * 2%:R + t))
  \/ (forall x, f(x) = 0).

Theorem IMO1_complete (f: int -> int): IMO1_problem f -> IMO1_solution f.
Proof.
  move=> H.
  have H1 : (forall a : int, f(a*2%:R) + f(0) = f(a)*2%:R).
    move=> a; apply/eqP; rewrite eq_sym -subr_eq -(addrKA (f 0)) subr_eq -mulr2n.
    by rewrite -[f 0 *+ _]mulr_natr -{1}addrC -(mul0r 2%:R) !H add0r mul0r addr0.
  have H2 : (forall a b c d : int, a + b = c + d -> f(a) + f(b) = f(c) + f(d)).
  move=> a b c d abcd_eq; apply: (@mulrIz int_numDomainType 2%:R); first by [].
  rewrite -![2%:R *~ _]mulrzl !intz !mulrDl -[f(a)*_]H1 -[f(c)*_]H1 -![_ + f 0]addrC.
  by rewrite -!addrA; congr(_ + _); rewrite !H abcd_eq.
  have H3 : (forall a : int, f(a) = (f(1) - f(0))*a + f(0)).
  elim/int_ind => [| n IHn| n IHn]; first by rewrite mulr0 add0r.
  rewrite !intS; have H4 : f(0) + f(n.+1) = f(1) + f(n) by apply H2.
  rewrite -(addr0 (f (1 + n%:Z))) -{1}(subrr (f 0)) addrA [_ + f 0]addrC H4 IHn.
  rewrite !mulrDl !mulrDr !mulr1 -(addrA (f 1 * n)) (addrA (f 1)).
  rewrite -2?(addrA (f 1 + f 1 * n)); congr(_ + _); by rewrite addrC addrA.
  rewrite !intS; have H5 : f(1) + f(-(1 + n%:Z)) = f(0) + f(-n%:Z).
    by apply H2; rewrite -{1}(add0r 1) addrKA.
  rewrite -(addr0 (f (-(1 + n%:Z)))) -{1}(subrr (f 1)) addrA [_ + f 1]addrC H5 IHn.
  rewrite !mulrDl addrA addrC (addrC (f 0)) 3?addrA -{1}(mulr1 (f 1)) -mulrN.
  rewrite -{2 3 5}(mulr1 (f 0)) !mulrNN -2?addrA -[in RHS]addrA; congr(_ + _).
    by rewrite -mulrDr; congr(_ * _); apply/eqP; rewrite -addr_eq0 (addrC 1) subrKA.
  rewrite -!mulrDr; congr(_ * _); by rewrite addrA (addrC n%:Z).
  move:(H 0 0); rewrite mul0r add0r [in f(f(_))]H3 mulrC -{1 5}(mul1r (f 0)) -!mulrDl.
  set f00 := (f 0 == 0); have H6 : ((f 0 == 0) = f00) by [].
  case: f00 H6 => /eqP; rewrite ?eqb_id ?eqbF_neg; move=> H6.
    move=> _; move: (H 0 1); rewrite [in f(f(_))]H3 H6 subr0 !add0r addr0.
    set f10 := (f 1 == 0); have H7 : ((f 1 == 0) = f10) by [].
    case: f10 H7 => /eqP; move=> H8.
      move=> _; right; move=> x; by rewrite H3 H6 H8 subr0 mul0r.
    move=> H9; have H10: f 1 = 2.
      apply: (@mulrIz int_numDomainType (f 1)); first by apply/eqP.
      by rewrite -![(f 1) *~ _]mulrzl !intz -H9 mulrC.
    left; exists 0; move=> x; by rewrite H3 H6 H10 subr0 !addr0 mulrC.
  move=> H11; left; exists (f 0); move=> x; rewrite H3 mulrC; congr((_ * _) + _).
  apply/eqP; rewrite -(addr0 (f 1 - f 0)) -{2}(subrr 1) addrA subr_eq eq_sym addrC.
  apply/eqP; apply: (@mulrIz int_numDomainType (f 0)) ; first by apply/eqP.
     by rewrite -![(f 0) *~ _]mulrzl !intz -H11 mulrC.
Qed.

Theorem IMO1_sound (f: int -> int): IMO1_solution f -> IMO1_problem f.
Proof.
  move=> [[t H] | H] a b; rewrite !H; last by rewrite mul0r.
  rewrite !mulrDl -!(addrA (a * 2 * 2)); congr(_ + _); by rewrite addrC.
Qed.
