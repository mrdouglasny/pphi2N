/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trace of product with elementary matrices
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Normed

noncomputable section

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Elementary matrix: 1 at (x,x), 0 elsewhere. -/
def Pphi2N.elemMatrix' (x : Λ) : Matrix Λ Λ ℝ :=
  Matrix.diagonal (Pi.single x 1)

set_option maxHeartbeats 400000 in
/-- Tr(M · E_x · N · E_y) = M_{yx} · N_{xy}. -/
theorem Pphi2N.trace_elemMatrix_product' (M N : Matrix Λ Λ ℝ) (x y : Λ) :
    Matrix.trace (M * Pphi2N.elemMatrix' x * N * Pphi2N.elemMatrix' y) = M y x * N x y := by
  simp only [Pphi2N.elemMatrix', Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply,
    mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end
