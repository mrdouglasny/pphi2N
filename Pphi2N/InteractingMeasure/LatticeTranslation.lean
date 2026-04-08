/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Translation Invariance of the O(N) Interaction

Proves that the O(N) lattice interaction V(φ) = Σ_x :P(|φ(x)|²):_c
is invariant under lattice translations: V(T_v φ) = V(φ).

This is the key ingredient for OS2 (translation invariance).

## Proof

The interaction is a sum over all lattice sites. Translating the field
φ(x) → φ(x+v) reindexes the sum. Since the lattice is periodic
(ℤ/Mℤ)² and the sum runs over ALL sites, the reindexed sum equals
the original: Σ_x f(x+v) = Σ_x f(x) for any f on a finite group.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Pphi2N.InteractingMeasure.ONTorusMeasure

noncomputable section

open GaussianField MeasureTheory BigOperators

namespace Pphi2N

variable (N : ℕ) (hN : 1 ≤ N) (d M : ℕ) [NeZero M]

/-! ## Lattice translation on N-component fields -/

/-- Lattice translation by vector v on N-component fields.
(T_v φ)(i, x) = φ(i, x + v) — shifts each component by v. -/
def latticeTranslation (v : FinLatticeSites d M) :
    (Fin N → FinLatticeField d M) → (Fin N → FinLatticeField d M) :=
  fun φ i x => φ i (x + v)

/-- Lattice translation is involutive: T_v ∘ T_{-v} = id. -/
theorem latticeTranslation_comp_neg (v : FinLatticeSites d M) :
    latticeTranslation N d M v ∘ latticeTranslation N d M (-v) = id := by
  funext φ i x; simp [latticeTranslation, add_neg_cancel_right]

theorem latticeTranslation_neg_comp (v : FinLatticeSites d M) :
    latticeTranslation N d M (-v) ∘ latticeTranslation N d M v = id := by
  funext φ i x; simp [latticeTranslation, neg_add_cancel_right]

/-- Lattice translation as an equivalence. -/
def latticeTranslationEquiv (v : FinLatticeSites d M) :
    (Fin N → FinLatticeField d M) ≃ (Fin N → FinLatticeField d M) where
  toFun := latticeTranslation N d M v
  invFun := latticeTranslation N d M (-v)
  left_inv := congr_fun (latticeTranslation_neg_comp N d M v)
  right_inv := congr_fun (latticeTranslation_comp_neg N d M v)

/-! ## The interaction is translation-invariant -/

/-- |φ(x+v)|² = |(T_v φ)(x)|² — the squared norm is preserved. -/
theorem siteNormSq_translate (v : FinLatticeSites d M)
    (φ : Fin N → FinLatticeField d M) (x : FinLatticeSites d M) :
    siteNormSq N d M (latticeTranslation N d M v φ) x =
    siteNormSq N d M φ (x + v) := by
  simp [siteNormSq, latticeTranslation]

/-- **The O(N) interaction is translation-invariant: V(T_v φ) = V(φ).**

V(T_v φ) = a^d · Σ_x :P(|(T_v φ)(x)|²):_c
          = a^d · Σ_x :P(|φ(x+v)|²):_c     (by definition of T_v)
          = a^d · Σ_y :P(|φ(y)|²):_c         (reindex y = x+v)
          = V(φ) -/
theorem onInteraction_translation_invariant (P : ONInteraction) (c a : ℝ)
    (v : FinLatticeSites d M)
    (φ : Fin N → FinLatticeField d M) :
    onInteraction N d M P c a (latticeTranslation N d M v φ) =
    onInteraction N d M P c a φ := by
  unfold onInteraction
  congr 1
  -- Σ_x :P(|(T_v φ)(x)|²):_c = Σ_x :P(|φ(x+v)|²):_c = Σ_y :P(|φ(y)|²):_c
  conv_lhs =>
    arg 2; ext x
    rw [siteNormSq_translate]
  -- Reindex the sum: Σ_x f(x+v) = Σ_y f(y) on a finite group
  exact Fintype.sum_equiv (Equiv.addRight v) _ _ (fun x => rfl)

end Pphi2N

end
