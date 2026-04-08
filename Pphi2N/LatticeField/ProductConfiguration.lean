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
  sorry -- Σⱼ Tⱼ((update 0 i g) j) = Tᵢ(g) by Finset.sum_ite_eq' + map_zero

theorem prodConfig_right_inv (T : Configuration (Fin N → E)) :
    prodConfigToFun (prodConfigInv T) = T := by
  sorry -- f = Σᵢ update 0 i (f i), then T(f) = Σᵢ T(update 0 i (f i)) by linearity

end Pphi2N

end
