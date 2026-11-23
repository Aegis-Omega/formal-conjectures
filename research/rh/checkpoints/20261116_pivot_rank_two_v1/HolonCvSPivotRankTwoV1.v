(*
  AEGIS Omega, HOLON V5: CvS rational identity certificates.
  Source-bound candidate for Coq/Rocq. No claims about RH or Weil positivity.
  Standalone QArith module, intended as an algebraic kernel before a CoRN IR/CC
  transport. No axiom, admit, or opacity placeholder is used.
  STATUS: KERNEL NOT REPLAYED HERE (no coqc/rocq installed).
*)
From Coq Require Import QArith.QArith.
From Coq Require Import Ring.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope Q_scope.
Module HolonCvSPivotRankTwoV1.
(* x denotes omega^2; the same polynomials hold in any characteristic-0 field. *)
Definition denom (m x : Q) : Q := 1 + 4 * m * m * x.
Definition pivot0_num (m : Q) : Q := m - 1.
Definition pivot1_num (m x : Q) : Q := -m * (1 + 4 * x).
(* Real and imaginary parts of the CLEARED complex moment numerator:
   v0 (s+i omega)(s+i m omega) + v1 s(s+i m omega)
      + denom s(s+i omega), where v0=pivot0_num, v1=pivot1_num.
   No division is used; the proof is a universal polynomial identity. *)
Definition cleared_real (m x s : Q) : Q :=
  pivot0_num m * (s * s - m * x) +
  pivot1_num m x * s * s + denom m x * s * s.
Definition cleared_imag_factor (m x : Q) : Q :=
  pivot0_num m * (m + 1) + pivot1_num m x * m + denom m x.
Theorem real_numerator_factor : forall m x s : Q,
  cleared_real m x s == m * (m - 1) * x * (4 * s * s - 1).
Proof. intros m x s. unfold cleared_real, pivot0_num, pivot1_num, denom. ring. Qed.
Theorem imaginary_numerator_zero : forall m x : Q,
  cleared_imag_factor m x == 0.
Proof. intros m x. unfold cleared_imag_factor, pivot0_num, pivot1_num, denom. ring. Qed.
Theorem positive_half_real_zero : forall m x : Q,
  cleared_real m x (1#2) == 0.
Proof. intros m x. unfold cleared_real, pivot0_num, pivot1_num, denom. ring. Qed.
Theorem negative_half_real_zero : forall m x : Q,
  cleared_real m x (-(1#2)) == 0.
Proof. intros m x. unfold cleared_real, pivot0_num, pivot1_num, denom. ring. Qed.
(* A 2x2 rank-two Gram update H = [[1+a,b],[b,1+c]] has
   adjugate Adj = [[1+c,-b],[-b,1+a]]. *)
Definition det2 (a b c : Q) : Q := (1 + a) * (1 + c) - b * b.
Theorem adjugate_00 : forall a b c : Q,
  (1 + a) * (1 + c) + b * (-b) == det2 a b c.
Proof. intros a b c. unfold det2. ring. Qed.
Theorem adjugate_01 : forall a b c : Q,
  (1 + a) * (-b) + b * (1 + a) == 0.
Proof. intros a b c. ring. Qed.
Theorem adjugate_10 : forall a b c : Q,
  b * (1 + c) + (1 + c) * (-b) == 0.
Proof. intros a b c. ring. Qed.
Theorem adjugate_11 : forall a b c : Q,
  b * (-b) + (1 + c) * (1 + a) == det2 a b c.
Proof. intros a b c. unfold det2. ring. Qed.
(* Explicit Cauchy-Binet sum of squares for the real pivot rows of U.
   Each list pair is one column of U. *)
Fixpoint gram00 (l : list (Q * Q)) : Q :=
  match l with
  | [] => 0
  | (x,y) :: tl => x * x + gram00 tl
  end.
Fixpoint gram01 (l : list (Q * Q)) : Q :=
  match l with
  | [] => 0
  | (x,y) :: tl => x * y + gram01 tl
  end.
Fixpoint gram11 (l : list (Q * Q)) : Q :=
  match l with
  | [] => 0
  | (x,y) :: tl => y * y + gram11 tl
  end.
Fixpoint cross_terms (x y : Q) (l : list (Q * Q)) : Q :=
  match l with
  | [] => 0
  | (u,v) :: tl => (x*v - y*u) * (x*v - y*u) + cross_terms x y tl
  end.
Fixpoint minors (l : list (Q * Q)) : Q :=
  match l with
  | [] => 0
  | (x,y) :: tl => cross_terms x y tl + minors tl
  end.
Lemma cross_terms_factor : forall (x y : Q) (l : list (Q * Q)),
  cross_terms x y l ==
    x*x*gram11 l + y*y*gram00 l - 2*x*y*gram01 l.
Proof.
  intros x y l.
  induction l as [| [u v] tl IH]; simpl.
  - ring.
  - setoid_rewrite IH. ring.
Qed.
Theorem lagrange_minors : forall l : list (Q * Q),
  gram00 l * gram11 l - gram01 l * gram01 l == minors l.
Proof.
  intro l.
  induction l as [| [x y] tl IH]; simpl.
  - ring.
  - setoid_rewrite (cross_terms_factor x y tl).
    setoid_rewrite <- IH.
    ring.
Qed.
Theorem gram_determinant_sos : forall l : list (Q * Q),
  det2 (gram00 l) (gram01 l) (gram11 l) ==
    1 + gram00 l + gram11 l + minors l.
Proof.
  intro l.
  unfold det2.
  setoid_rewrite <- (lagrange_minors l).
  ring.
Qed.
End HolonCvSPivotRankTwoV1.
