import Mathlib

#eval Lean.versionString

/-!
# OEIS A112521 — complete Formal Conjectures proof

The proof identifies the recursive array with coefficients of a transformed
homogeneous Fibonacci polynomial.  Its diagonal becomes the signed binomial
sum defining `a`.  A Wilf–Zeilberger certificate supplies a positive
recurrence for that sum, which discharges the `Int.toNat` boundary.
-/

namespace OeisA112521

open Nat Int Finset

/-- The alternating binomial sum in the Formal Conjectures target. -/
def a (n : ℕ) : ℕ :=
  (∑ j ∈ range n,
    let c1 : ℕ := (2 * j).choose j
    let c2Top : ℕ := 2 * n - (j + 2)
    let c2Bot : ℕ := n - (j + 1)
    let c2 : ℕ := c2Top.choose c2Bot
    let termMagnitude : ℤ := c1 * c2
    if j % 2 = 0 then termMagnitude else -termMagnitude
  ).toNat

/-- The recursively defined array in the Formal Conjectures target. -/
def T (n k : ℕ) : ℤ :=
  if n = 0 ∨ k = 0 then 0
  else if n = 1 ∧ k = 1 then 1
  else
    T n (k - 2) + T n (k - 1) - 2 * T (n - 1) (k - 1) +
      T (n - 1) k + T (n - 2) k
termination_by n + k

end OeisA112521

open Nat Int Finset

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace OeisA112521Proof

open MvPolynomial

abbrev P := MvPolynomial (Fin 2) ℤ

def e (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

def v : P := X 0
def u : P := X 1
def x : P := X 0
def y : P := X 1

/-- The homogeneous degree-`m` part of `1 / (1 - v - u²)`. -/
def H : ℕ → P
  | 0 => 1
  | 1 => v
  | m + 2 => v * H (m + 1) + u ^ 2 * H m

def linearChange : P →ₐ[ℤ] P :=
  MvPolynomial.aeval ![x + y, x - y]

def K (m : ℕ) : P := linearChange (H m)

lemma e_apply_zero (i j : ℕ) : e i j 0 = i := by
  simp [e]

lemma e_apply_one (i j : ℕ) : e i j 1 = j := by
  simp [e]

lemma e_add_zero (i j : ℕ) :
    e (i + 1) j = Finsupp.single 0 1 + e i j := by
  ext q
  fin_cases q <;> simp [e, Nat.add_comm]

lemma e_add_one (i j : ℕ) :
    e i (j + 1) = Finsupp.single 1 1 + e i j := by
  ext q
  fin_cases q <;> simp [e, Nat.add_comm]

lemma coeff_x_mul (p : P) (i j : ℕ) :
    coeff (e (i + 1) j) (x * p) = coeff (e i j) p := by
  rw [e_add_zero]
  simp [x]

lemma coeff_y_mul (p : P) (i j : ℕ) :
    coeff (e i (j + 1)) (y * p) = coeff (e i j) p := by
  rw [e_add_one]
  simp [y]

lemma coeff_x_mul' (p : P) (i j : ℕ) :
    coeff (e i j) (x * p) = if i = 0 then 0 else coeff (e (i - 1) j) p := by
  cases i with
  | zero => simp [x, e, MvPolynomial.coeff_X_mul']
  | succ i =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      simpa [Nat.succ_eq_add_one] using coeff_x_mul p i j

lemma coeff_y_mul' (p : P) (i j : ℕ) :
    coeff (e i j) (y * p) = if j = 0 then 0 else coeff (e i (j - 1)) p := by
  cases j with
  | zero => simp [y, e, MvPolynomial.coeff_X_mul']
  | succ j =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      simpa [Nat.succ_eq_add_one] using coeff_y_mul p i j

lemma coeff_x_sq_mul' (p : P) (i j : ℕ) :
    coeff (e i j) (x ^ 2 * p) =
      if i < 2 then 0 else coeff (e (i - 2) j) p := by
  rcases i with _ | _ | i <;>
    simp [pow_two, mul_assoc, coeff_x_mul']

lemma coeff_y_sq_mul' (p : P) (i j : ℕ) :
    coeff (e i j) (y ^ 2 * p) =
      if j < 2 then 0 else coeff (e i (j - 2)) p := by
  rcases j with _ | _ | j <;>
    simp [pow_two, mul_assoc, coeff_y_mul']

lemma coeff_xy_mul' (p : P) (i j : ℕ) :
    coeff (e i j) (x * y * p) =
      if i = 0 ∨ j = 0 then 0 else coeff (e (i - 1) (j - 1)) p := by
  rcases i with _ | i <;> rcases j with _ | j <;>
    simp [mul_assoc, coeff_x_mul', coeff_y_mul']

lemma coeff_two_mul (p : P) (i j : ℕ) :
    coeff (e i j) (2 * p) = 2 * coeff (e i j) p := by
  exact MvPolynomial.coeff_C_mul (e i j) (2 : ℤ) p

lemma coeff_linear_mul (p : P) (i j : ℕ) :
    coeff (e i j) ((x + y) * p) =
      (if i = 0 then 0 else coeff (e (i - 1) j) p) +
      (if j = 0 then 0 else coeff (e i (j - 1)) p) := by
  simp [add_mul, coeff_x_mul', coeff_y_mul']

lemma coeff_square_mul (p : P) (i j : ℕ) :
    coeff (e i j) ((x - y) ^ 2 * p) =
      (if i < 2 then 0 else coeff (e (i - 2) j) p) -
      2 * (if i = 0 ∨ j = 0 then 0 else coeff (e (i - 1) (j - 1)) p) +
      (if j < 2 then 0 else coeff (e i (j - 2)) p) := by
  have hid : (x - y) ^ 2 * p = x ^ 2 * p - 2 * (x * y * p) + y ^ 2 * p := by
    ring
  rw [hid, coeff_add, coeff_sub, coeff_x_sq_mul', coeff_y_sq_mul', coeff_two_mul,
    coeff_xy_mul']

lemma linearChange_v : linearChange v = x + y := by
  simp [linearChange, v]

lemma linearChange_u : linearChange u = x - y := by
  simp [linearChange, u]

lemma linearChange_X_zero : linearChange (X 0 : P) = x + y := linearChange_v
lemma linearChange_X_one : linearChange (X 1 : P) = x - y := linearChange_u

lemma K_zero : K 0 = 1 := by simp [K, H]

lemma K_one : K 1 = x + y := by simp [K, H, linearChange_v]

lemma K_add_two (m : ℕ) :
    K (m + 2) = (x + y) * K (m + 1) + (x - y) ^ 2 * K m := by
  simp [K, H, linearChange_v, linearChange_u]

def U (i j : ℕ) : ℤ := coeff (e i j) (K (i + j))

def C (n k : ℕ) : ℤ :=
  if n = 0 ∨ k = 0 then 0 else U (n - 1) (k - 1)

lemma C_zero_left (k : ℕ) : C 0 k = 0 := by simp [C]
lemma C_zero_right (n : ℕ) : C n 0 = 0 := by simp [C]
lemma C_one_one : C 1 1 = 1 := by simp [C, U, K_zero, e]
lemma C_succ_succ (i j : ℕ) : C (i + 1) (j + 1) = coeff (e i j) (K (i + j)) := by
  simp [C, U]

lemma C_rec_large (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hsum : 4 ≤ n + k) :
    C n k = C n (k - 2) + C n (k - 1) - 2 * C (n - 1) (k - 1) +
      C (n - 1) k + C (n - 2) k := by
  rcases n with _ | i
  · omega
  rcases k with _ | j
  · omega
  rw [C_succ_succ]
  rcases i with _ | _ | i
  · rcases j with _ | _ | j
    · omega
    · omega
    · rw [show 0 + (j + 1 + 1) = j + 2 by omega, K_add_two j, coeff_add,
        coeff_linear_mul, coeff_square_mul]
      simp [C, U]
      try (split_ifs <;> try omega)
      all_goals try simp only [Nat.add_comm, Nat.add_left_comm]
      all_goals ring
  · rcases j with _ | _ | j
    · omega
    · rw [show 1 + 1 = 0 + 2 by omega, K_add_two 0, coeff_add, coeff_linear_mul,
        coeff_square_mul]
      simp [C, U]
      try (split_ifs <;> try omega)
      all_goals try simp only [Nat.add_comm, Nat.add_left_comm]
      all_goals ring
    · rw [show 1 + (j + 1 + 1) = (j + 1) + 2 by omega, K_add_two (j + 1),
        coeff_add, coeff_linear_mul, coeff_square_mul]
      simp [C, U]
      try (split_ifs <;> try omega)
      all_goals try simp only [Nat.add_comm, Nat.add_left_comm]
      all_goals ring
  · rcases j with _ | _ | j
    · rw [show (i + 1 + 1) + 0 = i + 2 by omega, K_add_two i, coeff_add,
        coeff_linear_mul, coeff_square_mul]
      simp [C, U]
      try (split_ifs <;> try omega)
      all_goals try simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      all_goals ring
    · rw [show (i + 1 + 1) + 1 = (i + 1) + 2 by omega, K_add_two (i + 1),
        coeff_add, coeff_linear_mul, coeff_square_mul]
      simp [C, U]
      try (split_ifs <;> try omega)
      all_goals try simp only [Nat.add_comm, Nat.add_left_comm]
      all_goals ring
    · rw [show (i + 1 + 1) + (j + 1 + 1) = (i + j + 2) + 2 by omega,
        K_add_two (i + j + 2), coeff_add, coeff_linear_mul, coeff_square_mul]
      simp [C, U]
      try (split_ifs <;> try omega)
      all_goals try simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      all_goals ring

lemma C_equation (n k : ℕ) :
    C n k =
      if n = 0 ∨ k = 0 then 0
      else if n = 1 ∧ k = 1 then 1
      else C n (k - 2) + C n (k - 1) - 2 * C (n - 1) (k - 1) +
        C (n - 1) k + C (n - 2) k := by
  by_cases hn : n = 0
  · simp [hn, C]
  by_cases hk : k = 0
  · simp [hk, C]
  have hn1 : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  by_cases h11 : n = 1 ∧ k = 1
  · rcases h11 with ⟨rfl, rfl⟩
    simp [C_one_one]
  have hsum : 3 ≤ n + k := by omega
  by_cases hsmall : n + k = 3
  · have hor : (n = 1 ∧ k = 2) ∨ (n = 2 ∧ k = 1) := by omega
    rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [C, U, K_one, K_zero, e, x, y]
  · rw [if_neg (by simp [hn, hk]), if_neg h11]
    apply C_rec_large n k hn1 hk1
    omega

theorem T_eq_C (n k : ℕ) : OeisA112521.T n k = C n k := by
  induction hsum : n + k using Nat.strong_induction_on generalizing n k with
  | h s ih =>
      rw [OeisA112521.T, C_equation]
      split_ifs with hzero hone
      · rfl
      · rfl
      · rw [ih (n + (k - 2)) (by omega) n (k - 2) rfl,
          ih (n + (k - 1)) (by omega) n (k - 1) rfl,
          ih ((n - 1) + (k - 1)) (by omega) (n - 1) (k - 1) rfl,
          ih ((n - 1) + k) (by omega) (n - 1) k rfl,
          ih ((n - 2) + k) (by omega) (n - 2) k rfl]

lemma H_coeff (m j : ℕ) (hj : 2 * j ≤ m) :
    coeff (e (m - 2 * j) (2 * j)) (H m) = ((m - j).choose j : ℤ) := by
  induction m using Nat.twoStepInduction generalizing j with
  | zero =>
      have : j = 0 := by omega
      subst j
      simp [H, e]
  | one =>
      have : j = 0 := by omega
      subst j
      simp [H, v, e]
  | more m ihm ihm1 =>
      rw [H, coeff_add]
      change coeff (e (m + 2 - 2 * j) (2 * j)) (x * H (m + 1)) +
        coeff (e (m + 2 - 2 * j) (2 * j)) (y ^ 2 * H m) = _
      rw [coeff_x_mul', coeff_y_sq_mul']
      rcases j with _ | j
      · simp
        simpa using ihm1 0 (by omega)
      · by_cases hboundary : m + 2 = 2 * (j + 1)
        · have hm : m = 2 * j := by omega
          subst m
          rw [if_pos (by omega), zero_add]
          have hidx : 2 * j + 2 - 2 * (j + 1) = 0 := by omega
          have hpow : 2 * (j + 1) - 2 = 2 * j := by omega
          rw [if_neg (by omega), hidx, hpow]
          have hzero : 2 * j - 2 * j = 0 := by omega
          rw [← hzero, ihm j (by omega)]
          norm_cast
          have hleft : 2 * j - j = j := by omega
          have hright : 2 * j + 2 - (j + 1) = j + 1 := by omega
          rw [hleft, hright]
          simp
        · have hpos : 0 < m + 2 - 2 * (j + 1) := by omega
          have hj1 : 2 * (j + 1) ≤ m + 1 := by omega
          have hj0 : 2 * j ≤ m := by omega
          rw [if_neg (by omega), if_neg (by omega)]
          have hidx1 : m + 2 - 2 * (j + 1) - 1 = m + 1 - 2 * (j + 1) := by omega
          have hidx2 : m + 2 - 2 * (j + 1) = m - 2 * j := by omega
          have hpow : 2 * (j + 1) - 2 = 2 * j := by omega
          rw [hidx1, hidx2, hpow, ihm1 (j + 1) hj1, ihm j hj0]
          norm_cast
          have htop1 : m + 1 - (j + 1) = m - j := by omega
          have htopR : m + 2 - (j + 1) = (m - j) + 1 := by omega
          rw [htop1, htopR, Nat.choose_succ_succ]
          simp only [Nat.succ_eq_add_one, add_comm]

lemma coeff_pderiv (i : Fin 2) (m : Fin 2 →₀ ℕ) (p : P) :
    coeff m (MvPolynomial.pderiv i p) =
      ((m i + 1 : ℕ) : ℤ) * coeff (m + Finsupp.single i 1) p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial s a =>
      by_cases hs : s i = 0
      · have hne : s ≠ m + Finsupp.single i 1 := by
          intro h
          have hi := DFunLike.congr_fun h i
          simp [hs] at hi
        simp [MvPolynomial.pderiv_monomial, hs, MvPolynomial.coeff_monomial, hne]
      by_cases heq : s = m + Finsupp.single i 1
      · subst s
        simp [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
        ring
      · have hsub : s - Finsupp.single i 1 ≠ m := by
          intro h
          apply heq
          rw [← Finsupp.sub_add_single_one_cancel hs, h]
        simp [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, heq, hsub]

lemma coeff_iterate_pderiv (i : Fin 2) (m : Fin 2 →₀ ℕ) (n : ℕ) (p : P) :
    coeff m ((MvPolynomial.pderiv i : P → P)^[n] p) =
      (((m i + 1).ascFactorial n : ℕ) : ℤ) *
        coeff (m + Finsupp.single i n) p := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', coeff_pderiv,
        ih (m + Finsupp.single i 1)]
      have hcoord : ((m + Finsupp.single i 1) : Fin 2 →₀ ℕ) i + 1 =
          (m i + 1) + 1 := by simp
      have hidx : (m + Finsupp.single i 1) + Finsupp.single i n =
          m + Finsupp.single i (n + 1) := by
        ext q
        by_cases hq : q = i
        · subst q
          simp
          omega
        · simp [hq]
      rw [hcoord, hidx]
      have hfac : (↑(m i + 1) : ℤ) * ↑((m i + 2).ascFactorial n) =
          ↑((m i + 1).ascFactorial (n + 1)) := by
        norm_cast
        rw [Nat.succ_ascFactorial, Nat.ascFactorial_succ]
      rw [← mul_assoc, hfac]

lemma pderiv_zero_linearChange (p : P) :
    MvPolynomial.pderiv 0 (linearChange p) =
      linearChange (MvPolynomial.pderiv 0 p + MvPolynomial.pderiv 1 p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [linearChange]
  | add p q hp hq =>
      simp [hp, hq]
      ring
  | mul_X p i hp =>
      fin_cases i
      · simp [linearChange_X_zero, x, y, hp]
        ring
      · simp [linearChange_X_one, x, y, hp]
        ring

lemma pderiv_one_linearChange (p : P) :
    MvPolynomial.pderiv 1 (linearChange p) =
      linearChange (MvPolynomial.pderiv 0 p - MvPolynomial.pderiv 1 p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [linearChange]
  | add p q hp hq =>
      simp [hp, hq]
      ring
  | mul_X p i hp =>
      fin_cases i
      · simp [linearChange_X_zero, x, y, hp]
        ring
      · simp [linearChange_X_one, x, y, hp]
        ring

def A : Module.End ℤ P := (MvPolynomial.pderiv 0).toLinearMap
def B : Module.End ℤ P := (MvPolynomial.pderiv 1).toLinearMap

lemma A_apply (p : P) : A p = MvPolynomial.pderiv 0 p := rfl
lemma B_apply (p : P) : B p = MvPolynomial.pderiv 1 p := rfl

lemma pderiv_zero_one_comm (p : P) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p) =
      MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      fin_cases i <;> simp [hp] <;> ring

lemma A_mul_B : A * B = B * A := by
  apply LinearMap.ext
  intro p
  exact pderiv_zero_one_comm p

lemma A_linearChange (p : P) : A (linearChange p) = linearChange ((A + B) p) := by
  simpa [A, B] using pderiv_zero_linearChange p

lemma B_linearChange (p : P) : B (linearChange p) = linearChange ((A - B) p) := by
  simpa [A, B] using pderiv_one_linearChange p

lemma A_pow_linearChange (n : ℕ) (p : P) :
    (A ^ n) (linearChange p) = linearChange (((A + B) ^ n) p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, A_linearChange, ih, pow_succ,
        Module.End.mul_apply]

lemma B_pow_linearChange (n : ℕ) (p : P) :
    (B ^ n) (linearChange p) = linearChange (((A - B) ^ n) p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, B_linearChange, ih, pow_succ,
        Module.End.mul_apply]

lemma plus_minus_mul : (A + B) * (A - B) = A ^ 2 - B ^ 2 := by
  noncomm_ring [A_mul_B]

lemma plus_minus_comm : Commute (A + B) (A - B) := by
  show (A + B) * (A - B) = (A - B) * (A + B)
  noncomm_ring [A_mul_B]

lemma neg_B_sq_comm_A_sq : Commute (-(B ^ 2)) (A ^ 2) := by
  have hpow : Commute (B ^ 2) (A ^ 2) :=
    (show Commute B A from A_mul_B.symm).pow_pow 2 2
  exact hpow.neg_left

lemma operator_expansion (d : ℕ) :
    (A + B) ^ d * (A - B) ^ d =
      ∑ j ∈ range (d + 1),
        (-(B ^ 2)) ^ j * (A ^ 2) ^ (d - j) * d.choose j := by
  rw [← plus_minus_comm.mul_pow, plus_minus_mul]
  have hsub : A ^ 2 - B ^ 2 = -(B ^ 2) + A ^ 2 := by abel
  rw [hsub, neg_B_sq_comm_A_sq.add_pow]

lemma A_pow_apply (n : ℕ) (p : P) :
    (A ^ n) p = ((MvPolynomial.pderiv 0 : P → P)^[n] p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, A_apply, ih,
        Function.iterate_succ_apply]

lemma B_pow_apply (n : ℕ) (p : P) :
    (B ^ n) p = ((MvPolynomial.pderiv 1 : P → P)^[n] p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, B_apply, ih,
        Function.iterate_succ_apply]

lemma coeff_zero_Bpow_Apow (r s : ℕ) (p : P) :
    coeff 0 ((B ^ s * A ^ r) p) =
      (s.factorial : ℤ) * (r.factorial : ℤ) * coeff (e r s) p := by
  have hidx : Finsupp.single (1 : Fin 2) s + Finsupp.single 0 r = e r s := by
    ext i
    fin_cases i <;> simp [e]
  rw [Module.End.mul_apply, B_pow_apply, coeff_iterate_pderiv,
    A_pow_apply, coeff_iterate_pderiv]
  simp [Nat.one_ascFactorial, hidx, mul_assoc]

lemma coeff_zero_linearChange (p : P) :
    coeff 0 (linearChange p) = coeff 0 p := by
  change constantCoeff (linearChange p) = constantCoeff p
  induction p using MvPolynomial.induction_on with
  | C a => simp [linearChange]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      fin_cases i <;> simp [linearChange_X_zero, linearChange_X_one, x, y, hp]

lemma neg_one_end_pow_apply (j : ℕ) (p : P) :
    ((-1 : Module.End ℤ P) ^ j) p = ((-1 : ℤ) ^ j) • p := by
  induction j generalizing p with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, Module.End.mul_apply, pow_succ]
      simp [ih]

lemma nat_cast_end_apply (n : ℕ) (p : P) :
    ((n : Module.End ℤ P) p) = (n : ℤ) • p := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.cast_succ, ih, add_smul]

lemma operator_term_coeff (d j : ℕ) (hj : j ≤ d) :
    coeff 0 (((-(B ^ 2)) ^ j * (A ^ 2) ^ (d - j)) (H (2 * d))) =
      (-1 : ℤ) ^ j * ((2 * j).factorial : ℤ) *
        ((2 * (d - j)).factorial : ℤ) * ((2 * d - j).choose j : ℤ) := by
  have hidx : 2 * d - 2 * j = 2 * (d - j) := by omega
  have hcoeff : coeff (e (2 * (d - j)) (2 * j)) (H (2 * d)) =
      ((2 * d - j).choose j : ℤ) := by
    rw [← hidx]
    exact H_coeff (2 * d) j (by omega)
  rw [neg_pow, ← pow_mul, ← pow_mul, mul_assoc, Module.End.mul_apply,
    neg_one_end_pow_apply]
  rw [MvPolynomial.coeff_smul, smul_eq_mul, coeff_zero_Bpow_Apow]
  rw [hcoeff]
  ring

lemma double_derivative_linearChange (d : ℕ) (p : P) :
    (B ^ d * A ^ d) (linearChange p) =
      linearChange (((A + B) ^ d * (A - B) ^ d) p) := by
  rw [Module.End.mul_apply, A_pow_linearChange, B_pow_linearChange,
    Module.End.mul_apply]
  have hcomm := (plus_minus_comm.pow_pow d d).eq
  apply congrArg linearChange
  exact DFunLike.congr_fun hcomm.symm p

lemma factorial_sq_C_eq_raw_sum (d : ℕ) :
    (d.factorial : ℤ) ^ 2 * C (d + 1) (d + 1) =
      ∑ j ∈ range (d + 1),
        (d.choose j : ℤ) * (-1 : ℤ) ^ j * ((2 * j).factorial : ℤ) *
          ((2 * (d - j)).factorial : ℤ) * ((2 * d - j).choose j : ℤ) := by
  calc
    (d.factorial : ℤ) ^ 2 * C (d + 1) (d + 1) =
        coeff 0 ((B ^ d * A ^ d) (K (2 * d))) := by
          rw [C_succ_succ]
          have hsum : d + d = 2 * d := by omega
          rw [hsum, coeff_zero_Bpow_Apow]
          ring
    _ = coeff 0
        (linearChange (((A + B) ^ d * (A - B) ^ d) (H (2 * d)))) := by
          exact congrArg (coeff 0) (double_derivative_linearChange d (H (2 * d)))
    _ = coeff 0 (((A + B) ^ d * (A - B) ^ d) (H (2 * d))) :=
      coeff_zero_linearChange _
    _ = ∑ j ∈ range (d + 1),
        (d.choose j : ℤ) * (-1 : ℤ) ^ j * ((2 * j).factorial : ℤ) *
          ((2 * (d - j)).factorial : ℤ) * ((2 * d - j).choose j : ℤ) := by
      rw [operator_expansion]
      rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
      apply sum_congr rfl
      intro j hj
      have hjd : j ≤ d := by simpa using (mem_range.mp hj)
      rw [Module.End.mul_apply, nat_cast_end_apply, map_smul,
        MvPolynomial.coeff_smul, smul_eq_mul]
      rw [operator_term_coeff d j hjd]
      ring

lemma factorial_choose_identity_nat (d j : ℕ) (hj : j ≤ d) :
    d.choose j * (2 * j).factorial * (2 * (d - j)).factorial *
        (2 * d - j).choose j =
      d.factorial ^ 2 * (2 * j).choose j * (2 * d - j).choose (d - j) := by
  have hdj := Nat.choose_mul_factorial_mul_factorial hj
  have hcentral := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
  have htopj := Nat.choose_mul_factorial_mul_factorial
    (show j ≤ 2 * d - j by omega)
  have htopd := Nat.choose_mul_factorial_mul_factorial
    (show d - j ≤ 2 * d - j by omega)
  have hcentral' : (2 * j).choose j * j.factorial * j.factorial =
      (2 * j).factorial := by
    simpa [show 2 * j - j = j by omega] using hcentral
  have htopj' : (2 * d - j).choose j * j.factorial *
      (2 * (d - j)).factorial = (2 * d - j).factorial := by
    simpa [show 2 * d - j - j = 2 * (d - j) by omega] using htopj
  have htopd' : (2 * d - j).choose (d - j) * (d - j).factorial *
      d.factorial = (2 * d - j).factorial := by
    simpa [show 2 * d - j - (d - j) = d by omega] using htopd
  calc
    d.choose j * (2 * j).factorial * (2 * (d - j)).factorial *
        (2 * d - j).choose j =
      d.choose j * ((2 * j).choose j * j.factorial * j.factorial) *
        (2 * (d - j)).factorial * (2 * d - j).choose j := by rw [hcentral']
    _ = (2 * j).choose j * (d.choose j * j.factorial) *
        ((2 * d - j).choose j * j.factorial * (2 * (d - j)).factorial) := by ring
    _ = (2 * j).choose j * (d.choose j * j.factorial) *
        (2 * d - j).factorial := by rw [htopj']
    _ = (2 * j).choose j * (d.choose j * j.factorial) *
        ((2 * d - j).choose (d - j) * (d - j).factorial * d.factorial) := by
          rw [htopd']
    _ = (2 * j).choose j * (2 * d - j).choose (d - j) *
        (d.choose j * j.factorial * (d - j).factorial) * d.factorial := by ring
    _ = d.factorial ^ 2 * (2 * j).choose j *
        (2 * d - j).choose (d - j) := by rw [hdj]; ring

lemma factorial_choose_identity_int (d j : ℕ) (hj : j ≤ d) :
    (d.choose j : ℤ) * ((2 * j).factorial : ℤ) *
        ((2 * (d - j)).factorial : ℤ) * ((2 * d - j).choose j : ℤ) =
      (d.factorial : ℤ) ^ 2 * ((2 * j).choose j : ℤ) *
        ((2 * d - j).choose (d - j) : ℤ) := by
  exact_mod_cast factorial_choose_identity_nat d j hj

def S (d : ℕ) : ℤ :=
  ∑ j ∈ range (d + 1),
    (-1 : ℤ) ^ j * ((2 * j).choose j : ℤ) *
      ((2 * d - j).choose (d - j) : ℤ)

lemma C_diagonal_eq_S (d : ℕ) : C (d + 1) (d + 1) = S d := by
  have hscaled : (d.factorial : ℤ) ^ 2 * C (d + 1) (d + 1) =
      (d.factorial : ℤ) ^ 2 * S d := by
    rw [factorial_sq_C_eq_raw_sum, S, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjd : j ≤ d := by simpa using (mem_range.mp hj)
    have hid := factorial_choose_identity_int d j hjd
    calc
      (d.choose j : ℤ) * (-1 : ℤ) ^ j * ((2 * j).factorial : ℤ) *
          ((2 * (d - j)).factorial : ℤ) * ((2 * d - j).choose j : ℤ) =
        (-1 : ℤ) ^ j * ((d.choose j : ℤ) * ((2 * j).factorial : ℤ) *
          ((2 * (d - j)).factorial : ℤ) * ((2 * d - j).choose j : ℤ)) := by ring
      _ = (-1 : ℤ) ^ j * ((d.factorial : ℤ) ^ 2 *
          ((2 * j).choose j : ℤ) * ((2 * d - j).choose (d - j) : ℤ)) := by
            rw [hid]
      _ = (d.factorial : ℤ) ^ 2 *
          ((-1 : ℤ) ^ j * ((2 * j).choose j : ℤ) *
            ((2 * d - j).choose (d - j) : ℤ)) := by ring
  have hfac : (d.factorial : ℤ) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero d)
  exact mul_left_cancel₀ hfac hscaled

lemma signed_term_eq_pow (j : ℕ) (z : ℤ) :
    (if j % 2 = 0 then z else -z) = (-1 : ℤ) ^ j * z := by
  rw [neg_one_pow_eq_ite]
  simp only [Nat.even_iff]
  split_ifs <;> ring

def Fq (n j : ℕ) : ℚ :=
  if j < n then
    (-1 : ℚ) ^ j * (2 * j).factorial * (2 * n - j - 2).factorial /
      (j.factorial ^ 2 * (n - j - 1).factorial * (n - 1).factorial)
  else 0

def Gq (n j : ℕ) : ℚ :=
  if j ≤ n + 1 then
    -((-1 : ℚ) ^ j) * j * (j - 2 : ℤ) * (j - 6 * n - 1 : ℤ) *
      (j - 2 * n + 1 : ℤ) * (2 * j).factorial * (2 * n - j - 2).factorial /
      (j.factorial ^ 2 * (n - j + 1).factorial * (n - 1).factorial)
  else 0

lemma wz_interior (n j : ℕ) (hn : 3 ≤ n) (hj : j < n) :
    5 * n * (n + 1) * Fq (n + 2) j -
        2 * n * (2 * n + 1) * Fq (n + 1) j -
        4 * (16 * n ^ 2 - 1) * Fq n j = Gq n (j + 1) - Gq n j := by
  simp only [Fq, Gq, if_pos hj, if_pos (show j < n + 1 by omega),
    if_pos (show j < n + 2 by omega), if_pos (show j ≤ n + 1 by omega),
    if_pos (show j + 1 ≤ n + 1 by omega)]
  have h1 : 2 * (n + 2) - j - 2 = (2 * n - j - 3) + 5 := by omega
  have h2 : n + 2 - j - 1 = (n - j - 1) + 2 := by omega
  have h3 : n + 2 - 1 = (n - 1) + 2 := by omega
  have h4 : 2 * (n + 1) - j - 2 = (2 * n - j - 3) + 3 := by omega
  have h5 : n + 1 - j - 1 = (n - j - 1) + 1 := by omega
  have h6 : n + 1 - 1 = (n - 1) + 1 := by omega
  have h7 : 2 * n - j - 2 = (2 * n - j - 3) + 1 := by omega
  have h8 : n - j + 1 = (n - j - 1) + 2 := by omega
  have h9 : 2 * n - (j + 1) - 2 = 2 * n - j - 3 := by omega
  have h10 : n - (j + 1) + 1 = (n - j - 1) + 1 := by omega
  have h11 : 2 * (j + 1) = 2 * j + 2 := by omega
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  simp only [pow_succ]
  field_simp
  norm_num [Nat.factorial_succ]
  have hbq : ((2 * n - j - 3 : ℕ) : ℚ) = 2 * (n : ℚ) - (j : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ 2 * n - j),
      Nat.cast_sub (by omega : j ≤ 2 * n)]
    push_cast
    norm_num
  have hcq : ((n - j - 1 : ℕ) : ℚ) = (n : ℚ) - (j : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - j),
      Nat.cast_sub (by omega : j ≤ n)]
    norm_num
  have hnq : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hbq, hcq, hnq]
  ring

lemma wz_at_n (n : ℕ) (hn : 3 ≤ n) :
    5 * n * (n + 1) * Fq (n + 2) n -
        2 * n * (2 * n + 1) * Fq (n + 1) n -
        4 * (16 * n ^ 2 - 1) * Fq n n = Gq n (n + 1) - Gq n n := by
  simp only [Fq, Gq, if_neg (show ¬n < n by omega),
    if_pos (show n < n + 1 by omega), if_pos (show n < n + 2 by omega),
    if_pos (show n ≤ n + 1 by omega), if_pos (show n + 1 ≤ n + 1 by omega)]
  have h1 : 2 * (n + 2) - n - 2 = n + 2 := by omega
  have h2 : n + 2 - n - 1 = 1 := by omega
  have h3 : n + 2 - 1 = n + 1 := by omega
  have h4 : 2 * (n + 1) - n - 2 = n := by omega
  have h5 : n + 1 - n - 1 = 0 := by omega
  have h6 : n + 1 - 1 = n := by omega
  have h7 : n - n + 1 = 1 := by omega
  have h8 : 2 * n - n - 2 = n - 2 := by omega
  have h9 : n - (n + 1) + 1 = 1 := by omega
  have h10 : 2 * n - (n + 1) - 2 = n - 3 := by omega
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  simp only [pow_succ]
  field_simp
  norm_num [Nat.factorial_succ]
  have hfacn : n.factorial = n * (n - 1).factorial := by
    simpa [show n - 1 + 1 = n by omega] using Nat.factorial_succ (n - 1)
  have hfacnm1 : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
    simpa [show n - 2 + 1 = n - 1 by omega] using Nat.factorial_succ (n - 2)
  have hfacnm2 : (n - 2).factorial = (n - 2) * (n - 3).factorial := by
    simpa [show n - 3 + 1 = n - 2 by omega] using Nat.factorial_succ (n - 3)
  have hfac2 : (2 * (n + 1)).factorial =
      (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
    conv_lhs =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Nat.factorial_succ,
        show 2 * n + 1 = 2 * n + 1 by rfl, Nat.factorial_succ]
    ring
  rw [hfac2, hfacn, hfacnm1, hfacnm2]
  norm_num
  have hnm1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hnm2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  rw [hnm1, hnm2]
  ring

lemma wz_at_n_add_one (n : ℕ) (hn : 3 ≤ n) :
    5 * n * (n + 1) * Fq (n + 2) (n + 1) -
        2 * n * (2 * n + 1) * Fq (n + 1) (n + 1) -
        4 * (16 * n ^ 2 - 1) * Fq n (n + 1) =
      Gq n (n + 2) - Gq n (n + 1) := by
  simp only [Fq, Gq, if_neg (show ¬n + 1 < n by omega),
    if_neg (show ¬n + 1 < n + 1 by omega),
    if_pos (show n + 1 < n + 2 by omega),
    if_pos (show n + 1 ≤ n + 1 by omega),
    if_neg (show ¬n + 2 ≤ n + 1 by omega)]
  have h1 : 2 * (n + 2) - (n + 1) - 2 = n + 1 := by omega
  have h2 : n + 2 - (n + 1) - 1 = 0 := by omega
  have h3 : n + 2 - 1 = n + 1 := by omega
  have h4 : n - (n + 1) + 1 = 1 := by omega
  have h5 : 2 * n - (n + 1) - 2 = n - 3 := by omega
  rw [h1, h2, h3, h4, h5]
  simp only [pow_succ]
  field_simp
  norm_num [Nat.factorial_succ]
  have hfacnm1 : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
    simpa [show n - 2 + 1 = n - 1 by omega] using Nat.factorial_succ (n - 2)
  have hfacnm2 : (n - 2).factorial = (n - 2) * (n - 3).factorial := by
    simpa [show n - 3 + 1 = n - 2 by omega] using Nat.factorial_succ (n - 3)
  rw [hfacnm1, hfacnm2]
  norm_num
  have hnm1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hnm2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  rw [hnm1, hnm2]
  ring

lemma wz_pointwise (n j : ℕ) (hn : 3 ≤ n) (hj : j < n + 2) :
    5 * n * (n + 1) * Fq (n + 2) j -
        2 * n * (2 * n + 1) * Fq (n + 1) j -
        4 * (16 * n ^ 2 - 1) * Fq n j = Gq n (j + 1) - Gq n j := by
  by_cases hlt : j < n
  · exact wz_interior n j hn hlt
  have hj_cases : j = n ∨ j = n + 1 := by omega
  rcases hj_cases with h | h
  · subst j
    exact wz_at_n n hn
  · subst j
    exact wz_at_n_add_one n hn

def Aq (n : ℕ) : ℚ := ∑ j ∈ range n, Fq n j

lemma sum_Fq_pad_one (n : ℕ) :
    (∑ j ∈ range (n + 1), Fq n j) = Aq n := by
  rw [sum_range_succ]
  simp [Aq, Fq]

lemma sum_Fq_pad_two (n : ℕ) :
    (∑ j ∈ range (n + 2), Fq n j) = Aq n := by
  rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ, sum_Fq_pad_one]
  simp [Fq]

lemma Aq_recurrence (n : ℕ) (hn : 3 ≤ n) :
    5 * n * (n + 1) * Aq (n + 2) =
      2 * n * (2 * n + 1) * Aq (n + 1) +
        4 * (16 * n ^ 2 - 1) * Aq n := by
  have hwz :
      (∑ j ∈ range (n + 2),
        (5 * n * (n + 1) * Fq (n + 2) j -
          2 * n * (2 * n + 1) * Fq (n + 1) j -
          4 * (16 * n ^ 2 - 1) * Fq n j)) =
      ∑ j ∈ range (n + 2), (Gq n (j + 1) - Gq n j) := by
    apply sum_congr rfl
    intro j hj
    exact wz_pointwise n j hn (mem_range.mp hj)
  rw [sum_sub_distrib, sum_sub_distrib] at hwz
  simp only [← mul_sum] at hwz
  rw [sum_Fq_pad_two n, sum_Fq_pad_one (n + 1)] at hwz
  change
    5 * (n : ℚ) * (n + 1) * Aq (n + 2) -
        2 * n * (2 * n + 1) * Aq (n + 1) -
        4 * (16 * n ^ 2 - 1) * Aq n = _ at hwz
  rw [Finset.sum_range_sub] at hwz
  have hG0 : Gq n 0 = 0 := by simp [Gq]
  have hGend : Gq n (n + 2) = 0 := by simp [Gq]
  rw [hG0, hGend] at hwz
  linarith

lemma Fq_eq_choose (n j : ℕ) (hj : j < n) :
    Fq n j = (-1 : ℚ) ^ j * ((2 * j).choose j : ℚ) *
      ((2 * n - j - 2).choose (n - j - 1) : ℚ) := by
  have hc := Nat.choose_mul_factorial_mul_factorial
    (show j ≤ 2 * j by omega)
  have hc' : (2 * j).choose j * j.factorial * j.factorial =
      (2 * j).factorial := by
    simpa [show 2 * j - j = j by omega] using hc
  have ht := Nat.choose_mul_factorial_mul_factorial
    (show n - j - 1 ≤ 2 * n - j - 2 by omega)
  have ht' : (2 * n - j - 2).choose (n - j - 1) *
      (n - j - 1).factorial * (n - 1).factorial =
        (2 * n - j - 2).factorial := by
    simpa [show 2 * n - j - 2 - (n - j - 1) = n - 1 by omega] using ht
  have hcq : ((2 * j).choose j : ℚ) * j.factorial * j.factorial =
      (2 * j).factorial := by exact_mod_cast hc'
  have htq : ((2 * n - j - 2).choose (n - j - 1) : ℚ) *
      (n - j - 1).factorial * (n - 1).factorial =
        (2 * n - j - 2).factorial := by exact_mod_cast ht'
  rw [Fq, if_pos hj, ← hcq, ← htq]
  field_simp

lemma Aq_eq_S (n : ℕ) (hn : 1 ≤ n) : Aq n = (S (n - 1) : ℚ) := by
  rw [Aq, S]
  push_cast
  rw [show n - 1 + 1 = n by omega]
  apply sum_congr rfl
  intro j hj
  have hjn : j < n := mem_range.mp hj
  have htop : 2 * (n - 1) - j = 2 * n - j - 2 := by omega
  have hbot : n - 1 - j = n - j - 1 := by omega
  rw [Fq_eq_choose n j hjn, htop, hbot]

lemma S_recurrence_Q (n : ℕ) (hn : 3 ≤ n) :
    5 * n * (n + 1) * (S (n + 1) : ℚ) =
      2 * n * (2 * n + 1) * (S n : ℚ) +
        4 * (16 * n ^ 2 - 1) * (S (n - 1) : ℚ) := by
  have h := Aq_recurrence n hn
  rw [Aq_eq_S n (by omega), Aq_eq_S (n + 1) (by omega),
    Aq_eq_S (n + 2) (by omega)] at h
  norm_num at h ⊢
  convert h using 1

theorem S_nonneg (d : ℕ) : 0 ≤ S d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hd : d < 4
      · interval_cases d <;> norm_num [S, sum_range_succ, Nat.choose]
      · have hn : 3 ≤ d - 1 := by omega
        have hrec := S_recurrence_Q (d - 1) hn
        have hidx : d - 1 + 1 = d := by omega
        rw [hidx] at hrec
        have ih1z : 0 ≤ S (d - 1) := ih (d - 1) (by omega)
        have ih2z : 0 ≤ S (d - 2) := ih (d - 2) (by omega)
        have ih1 : (0 : ℚ) ≤ (S (d - 1) : ℚ) := by exact_mod_cast ih1z
        have ih2 : (0 : ℚ) ≤ (S (d - 2) : ℚ) := by exact_mod_cast ih2z
        have hm : (3 : ℚ) ≤ ((d - 1 : ℕ) : ℚ) := by exact_mod_cast hn
        have hfac : (0 : ℚ) <
            5 * (d - 1 : ℕ) * ((d - 1 : ℕ) + 1) := by positivity
        have hterm1 : (0 : ℚ) ≤
            2 * (d - 1 : ℕ) * (2 * (d - 1 : ℕ) + 1) *
              (S (d - 1) : ℚ) := by positivity
        have hcoef2 : (0 : ℚ) ≤
            4 * (16 * ((d - 1 : ℕ) : ℚ) ^ 2 - 1) := by
          nlinarith [sq_nonneg (((d - 1 : ℕ) : ℚ))]
        have hterm2 : (0 : ℚ) ≤
            4 * (16 * ((d - 1 : ℕ) : ℚ) ^ 2 - 1) *
              (S (d - 2) : ℚ) := mul_nonneg hcoef2 ih2
        have hSd : (0 : ℚ) ≤ (S d : ℚ) := by
          have hsub : d - 1 - 1 = d - 2 := by omega
          rw [hsub] at hrec
          nlinarith
        exact_mod_cast hSd

lemma a_succ_eq_toNat_S (d : ℕ) :
    OeisA112521.a (d + 1) = (S d).toNat := by
  unfold OeisA112521.a S
  congr 1
  apply sum_congr rfl
  intro j hj
  have hjd : j ≤ d := by simpa using mem_range.mp hj
  have htop : 2 * (d + 1) - (j + 2) = 2 * d - j := by omega
  have hbot : d + 1 - (j + 1) = d - j := by omega
  simp only
  rw [htop, hbot, signed_term_eq_pow]
  ring

/-- A hypothesis-free proof of the exact theorem statement in Formal Conjectures. -/
theorem formal_conjectures_target :
    ∀ (n : ℕ), n ≥ 1 → (OeisA112521.a n : ℤ) = OeisA112521.T n n := by
  intro n hn
  cases n with
  | zero => omega
  | succ d =>
      rw [a_succ_eq_toNat_S]
      have hcast : ((S d).toNat : ℤ) = S d := Int.toNat_of_nonneg (S_nonneg d)
      rw [hcast, T_eq_C, C_diagonal_eq_S]

end OeisA112521Proof

namespace OeisA112521Lean4Web

/-- The exact OEIS A112521 Formal Conjectures statement. -/
theorem conjecture :
    ∀ (n : ℕ), n ≥ 1 →
      (OeisA112521.a n : ℤ) = OeisA112521.T n n :=
  OeisA112521Proof.formal_conjectures_target

#print axioms conjecture

end OeisA112521Lean4Web
