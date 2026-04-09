/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ContDiff of Matrix.det (proved)

The determinant is C∞ by Leibniz formula: det is a polynomial in entries.
-/

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed

noncomputable section

set_option maxHeartbeats 400000 in
/-- **The determinant is C∞** as a function of the matrix entries. -/
theorem MatrixCalculus.contDiff_matrix_det_proved {n : Type*} [Fintype n] [DecidableEq n] :
    -- Use Pi norm (not linftyOp) to avoid norm mismatch
    @ContDiff ℝ _ (n → n → ℝ) Pi.normedAddCommGroup Pi.normedSpace ℝ _ _ ⊤
      (Matrix.det : Matrix n n ℝ → ℝ) := by
  have hdet : (Matrix.det : Matrix n n ℝ → ℝ) = fun A =>
      ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i := by
    ext A; exact Matrix.det_apply A
  rw [hdet]
  apply ContDiff.sum; intro σ _
  apply ContDiff.const_smul
  apply contDiff_prod; intro i _
  exact contDiff_pi.mp (contDiff_pi.mp contDiff_id (σ i)) i

end
