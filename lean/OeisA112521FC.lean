import OeisA112521Proof

/-!
# OEIS A112521: Formal Conjectures entry point

`conjecture_solved` has exactly the statement of
`FormalConjectures.OEIS.112521.OeisA112521.conjecture`.  The proof is defined
without using the upstream open theorem.
-/

namespace OeisA112521

/-- OEIS A112521, with the exact Formal Conjectures theorem statement. -/
@[category research solved, AMS 11]
theorem conjecture_solved :
    ∀ (n : ℕ), n ≥ 1 → (a n : ℤ) = T n n :=
  OeisA112521Proof.formal_conjectures_target

#print axioms conjecture_solved

end OeisA112521
