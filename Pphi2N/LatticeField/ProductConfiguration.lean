/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Product Configuration Spaces

Configuration (Fin N → E) ≅ (Fin N → Configuration E)

A functional T on (Fin N → E) acts by T(f) = Σᵢ Tᵢ(fᵢ).
The inverse extracts Tᵢ(g) = T(update 0 i g).
-/

import GaussianField.Construction

noncomputable section

open GaussianField

namespace Pphi2N

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {N : ℕ}

def prodConfigToFun (T : Fin N → Configuration E) :
    Configuration (Fin N → E) where
  toFun f := ∑ i : Fin N, T i (f i)
  map_add' f g := by simp [map_add, ← Finset.sum_add_distrib]
  map_smul' r f := by simp [map_smul, smul_eq_mul, Finset.mul_sum]
  cont := continuous_finset_sum _ fun i _ => (T i).cont.comp (continuous_apply i)

def prodConfigInv (T : Configuration (Fin N → E)) : Fin N → Configuration E :=
  fun i => {
    toFun := fun g => T (Function.update 0 i g)
    map_add' := fun g h => by
      simp only [← map_add]; congr 1; ext j
      simp [Function.update]; split_ifs <;> simp
    map_smul' := fun r g => by
      simp only [← map_smul]; congr 1; ext j
      simp [Function.update, smul_eq_mul]
    cont := T.cont.comp (continuous_const.update i continuous_id)
  }

theorem prodConfig_left_inv (T : Fin N → Configuration E) :
    prodConfigInv (prodConfigToFun T) = T := by
  funext i
  apply ContinuousLinearMap.ext
  intro g
  -- Goal: (prodConfigInv (prodConfigToFun T)) i g = T i g
  -- LHS = ∑ j, T j ((update 0 i g) j)
  show ∑ j : Fin N, T j (Function.update (0 : Fin N → E) i g j) = T i g
  rw [Finset.sum_eq_single i]
  · simp [Function.update_self]
  · intro j _ hji
    simp only [Function.update_of_ne hji, Pi.zero_apply, map_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem prodConfig_right_inv (T : Configuration (Fin N → E)) :
    prodConfigToFun (prodConfigInv T) = T := by
  apply ContinuousLinearMap.ext
  intro f
  -- Goal: (prodConfigToFun (prodConfigInv T)) f = T f
  -- LHS = ∑ i, T (update 0 i (f i))
  show ∑ i : Fin N, T (Function.update (0 : Fin N → E) i (f i)) = T f
  -- Key: f = ∑ i, update 0 i (f i) in the Pi type Fin N → E
  have h_decomp : f = ∑ i : Fin N, Function.update (0 : Fin N → E) i (f i) := by
    ext j
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp [Function.update_self]
    · intro i _ hij
      simp only [Function.update_of_ne (Ne.symm hij), Pi.zero_apply]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  conv_rhs => rw [h_decomp]
  rw [map_sum]

end Pphi2N

end
