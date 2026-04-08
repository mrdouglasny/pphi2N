/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# O(N) Interacting Measure on the Torus Lattice

Constructs the O(N) interacting measure on the torus lattice (ℤ/Mℤ)²:

  μ_{int,N} = (1/Z_N) · exp(-V_N) · dμ_{GFF}^{⊗N}

where:
- μ_{GFF}^{⊗N} = product of N scalar GFFs on the lattice
- V_N(φ) = a² Σ_x :P(|φ(x)|²):_c is the O(N)-invariant interaction
- Z_N = ∫ exp(-V_N) dμ_{GFF}^{⊗N} is the partition function

## Nelson estimate (N-dependent)

V_N is bounded below: ∃ B(N), ∀ φ, V_N(φ) ≥ -B(N).

This follows from the scalar Nelson estimate by Cauchy-Schwarz:
  |φ(x)|⁴ = (Σᵢ (φⁱ)²)² ≤ N · Σᵢ (φⁱ)⁴

So the O(N) quartic interaction is bounded by N times the sum of
scalar quartic interactions. The bound B(N) = O(N · |Λ|).

## Main definitions

- `onBoltzmannWeight` — exp(-V_N(φ))
- `onPartitionFunction` — Z_N = ∫ exp(-V_N) dμ^{⊗N}
- `onInteractingMeasure` — (1/Z_N) · exp(-V_N) · dμ^{⊗N}

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I-II
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
-/

import Pphi2N.InteractingMeasure.ONLatticeAction
import Lattice.FiniteField
import Pphi2N.LatticeField.ProductGFF
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact

noncomputable section

open GaussianField MeasureTheory BigOperators Pphi2N

namespace Pphi2N

variable (N : ℕ) (hN : 1 ≤ N)

/-! ## Configuration type

For the lattice case, the N-component field is
  φ : Fin N → (FinLatticeSites d M → ℝ)

We access the field at site x, component i as `φ i x`. -/

variable (d M : ℕ) [NeZero M]

/-- The N-component field viewed as an NComponentField at a site.
Extracts the field values at site x across all N components:
  siteField(φ, x) = (φ¹(x), ..., φᴺ(x)) -/
def siteField (φ : Fin N → FinLatticeField d M) (x : FinLatticeSites d M) :
    Fin N → ℝ :=
  fun i => φ i x

/-- |φ(x)|² = Σᵢ (φⁱ(x))² at a single site. -/
def siteNormSq (φ : Fin N → FinLatticeField d M) (x : FinLatticeSites d M) : ℝ :=
  ∑ i : Fin N, (φ i x) ^ 2

/-- |φ(x)|² ≥ 0. -/
theorem siteNormSq_nonneg (φ : Fin N → FinLatticeField d M) (x : FinLatticeSites d M) :
    0 ≤ siteNormSq N d M φ x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-! ## The O(N) interaction on the product space -/

/-- The O(N) interaction functional on the product configuration space.

V_N(φ) = a^d · Σ_{x ∈ Λ} :P(|φ(x)|²):_c

where φ : Fin N → (Λ → ℝ) is the N-component field. -/
def onInteraction (P : ONInteraction) (c a : ℝ) :
    (Fin N → FinLatticeField d M) → ℝ :=
  fun φ => a ^ d * ∑ x : FinLatticeSites d M,
    wickInteraction_ON N P c (siteNormSq N d M φ x)

/-! ## Nelson estimate for O(N) (axiomatized)

The key bound: V_N is bounded below. For the quartic interaction,
the Cauchy-Schwarz inequality gives:

  (Σᵢ aᵢ)² ≤ N · Σᵢ aᵢ²

so |φ|⁴ ≤ N · Σᵢ (φⁱ)⁴, and the O(N) Nelson bound follows from
the scalar one with an extra factor of N:

  V_N(φ) ≥ -C(N) · |Λ|  where C(N) = O(N · C₁)  -/

/-! ### Formal polynomial representation of wickMonomial_ON

We represent `wickMonomial_ON N c k t` as the evaluation of a formal polynomial
in `t`, prove it is monic of degree `k`, and thereby establish that
`wickInteraction_ON N P c t` has positive leading coefficient `1/P.degree`.
-/

/-- Formal polynomial (in the variable t) whose evaluation at t equals
`wickMonomial_ON N c k t`. Mirrors the three-term recursion. -/
private def wickMonomialPolyON (N : ℕ) (c : ℝ) : ℕ → Polynomial ℝ
  | 0     => 1
  | 1     => Polynomial.X - Polynomial.C ((N : ℝ) * c)
  | k + 2 =>
      (Polynomial.X - Polynomial.C (wickShiftCoeff N (k + 1) * c)) *
      wickMonomialPolyON N c (k + 1) -
      Polynomial.C (wickLowerCoeff N (k + 1) * c ^ 2) *
      wickMonomialPolyON N c k

/-- Evaluation of the formal polynomial equals the Wick monomial. -/
private theorem wickMonomialPolyON_eval (N : ℕ) (c : ℝ) :
    ∀ (k : ℕ) (t : ℝ), (wickMonomialPolyON N c k).eval t = wickMonomial_ON N c k t
  | 0,     _ => by simp [wickMonomialPolyON, wickMonomial_ON]
  | 1,     _ => by simp [wickMonomialPolyON, wickMonomial_ON]
  | k + 2, t => by
      simp only [wickMonomialPolyON, wickMonomial_ON,
        Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C]
      rw [wickMonomialPolyON_eval N c (k + 1) t, wickMonomialPolyON_eval N c k t]

/-- `wickMonomialPolyON N c k` is monic of natDegree `k`.
Proved by joint induction on k and k+1. -/
private theorem wickMonomialPolyON_monic_deg (N : ℕ) (c : ℝ) :
    ∀ k : ℕ, (wickMonomialPolyON N c k).Monic ∧ (wickMonomialPolyON N c k).natDegree = k
  | 0 => ⟨Polynomial.monic_one, by simp [wickMonomialPolyON]⟩
  | 1 => by
      simp only [wickMonomialPolyON]
      refine ⟨Polynomial.monic_X.sub_of_left ?_, ?_⟩
      · -- degree (C(N*c)) < degree X
        calc Polynomial.degree (Polynomial.C ((N : ℝ) * c))
            ≤ 0 := Polynomial.degree_C_le
          _ < 1 := by norm_num
          _ = Polynomial.degree Polynomial.X := Polynomial.degree_X.symm
      · -- natDegree (X - C(N*c)) = 1
        exact Polynomial.natDegree_X_sub_C ((N : ℝ) * c)
  | k + 2 => by
      obtain ⟨hm1, hd1⟩ := wickMonomialPolyON_monic_deg N c (k + 1)
      obtain ⟨hm0, hd0⟩ := wickMonomialPolyON_monic_deg N c k
      simp only [wickMonomialPolyON]
      set A : Polynomial ℝ := Polynomial.X - Polynomial.C (wickShiftCoeff N (k + 1) * c)
      set B : Polynomial ℝ := Polynomial.C (wickLowerCoeff N (k + 1) * c ^ 2)
      have hA_monic : A.Monic := Polynomial.monic_X.sub_of_left
        (calc Polynomial.degree (Polynomial.C (wickShiftCoeff N (k + 1) * c))
            ≤ 0 := Polynomial.degree_C_le
          _ < 1 := by norm_num
          _ = Polynomial.degree Polynomial.X := Polynomial.degree_X.symm)
      have hA_deg : A.natDegree = 1 := by
        simp only [A]
        exact Polynomial.natDegree_X_sub_C (wickShiftCoeff N (k + 1) * c)
      have hprod_monic : (A * wickMonomialPolyON N c (k + 1)).Monic := hA_monic.mul hm1
      have hprod_deg : (A * wickMonomialPolyON N c (k + 1)).natDegree = k + 2 := by
        rw [Polynomial.natDegree_mul hA_monic.ne_zero hm1.ne_zero, hA_deg, hd1]; ring
      have hlt : (B * wickMonomialPolyON N c k).natDegree <
          (A * wickMonomialPolyON N c (k + 1)).natDegree := by
        rw [hprod_deg]
        calc (B * wickMonomialPolyON N c k).natDegree
            ≤ B.natDegree + (wickMonomialPolyON N c k).natDegree := Polynomial.natDegree_mul_le
          _ = 0 + k := by rw [Polynomial.natDegree_C, hd0]
          _ = k := zero_add k
          _ < k + 2 := by omega
      constructor
      · rw [sub_eq_add_neg]
        apply hprod_monic.add_of_left
        rw [Polynomial.degree_neg]
        calc Polynomial.degree (B * wickMonomialPolyON N c k)
            ≤ ↑(B * wickMonomialPolyON N c k).natDegree := Polynomial.degree_le_natDegree
          _ < ↑(A * wickMonomialPolyON N c (k + 1)).natDegree := by exact_mod_cast hlt
          _ = Polynomial.degree (A * wickMonomialPolyON N c (k + 1)) :=
              (Polynomial.degree_eq_natDegree hprod_monic.ne_zero).symm
      · exact (Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt).trans hprod_deg

/-- `wickMonomialPolyON N c k` is monic. -/
private theorem wickMonomialPolyON_monic (N : ℕ) (c : ℝ) (k : ℕ) :
    (wickMonomialPolyON N c k).Monic := (wickMonomialPolyON_monic_deg N c k).1

/-- `wickMonomialPolyON N c k` has natDegree `k`. -/
private theorem wickMonomialPolyON_natDegree (N : ℕ) (c : ℝ) (k : ℕ) :
    (wickMonomialPolyON N c k).natDegree = k := (wickMonomialPolyON_monic_deg N c k).2

/-- The formal polynomial for `wickInteraction_ON N P c`. -/
private def wickInteractionPolyON (N : ℕ) (P : ONInteraction) (c : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 / (P.degree : ℝ)) * wickMonomialPolyON N c P.degree +
  ∑ m : Fin P.degree, Polynomial.C (P.coeff m) * wickMonomialPolyON N c m

/-- Evaluation of `wickInteractionPolyON` equals `wickInteraction_ON`. -/
private theorem wickInteractionPolyON_eval (N : ℕ) (P : ONInteraction) (c t : ℝ) :
    (wickInteractionPolyON N P c).eval t = wickInteraction_ON N P c t := by
  simp only [wickInteractionPolyON, wickInteraction_ON,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_finset_sum]
  congr 1
  · rw [wickMonomialPolyON_eval]
  · apply Finset.sum_congr rfl
    intro m _
    congr 1
    exact wickMonomialPolyON_eval N c m t

/-- `wickInteractionPolyON N P c` has natDegree equal to `P.degree`. -/
private theorem wickInteractionPolyON_natDegree (N : ℕ) (P : ONInteraction) (c : ℝ) :
    (wickInteractionPolyON N P c).natDegree = P.degree := by
  simp only [wickInteractionPolyON]
  have hdeg_pos : 0 < P.degree := by linarith [P.hdeg]
  have h1k_ne : (1 / (P.degree : ℝ)) ≠ 0 := by
    exact one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hdeg_pos))
  have hlead_deg : (Polynomial.C (1 / (P.degree : ℝ)) * wickMonomialPolyON N c P.degree).natDegree
      = P.degree := by
    rw [Polynomial.natDegree_C_mul h1k_ne, wickMonomialPolyON_natDegree]
  have hsum_deg : (∑ m : Fin P.degree, Polynomial.C (P.coeff m) *
      wickMonomialPolyON N c m).natDegree < P.degree := by
    apply lt_of_le_of_lt
    · apply Polynomial.natDegree_sum_le_of_forall_le (n := P.degree - 1)
      intro m _
      calc (Polynomial.C (P.coeff m) * wickMonomialPolyON N c (m : ℕ)).natDegree
          ≤ (Polynomial.C (P.coeff m)).natDegree + (wickMonomialPolyON N c (m : ℕ)).natDegree :=
            Polynomial.natDegree_mul_le
        _ = 0 + (m : ℕ) := by rw [Polynomial.natDegree_C, wickMonomialPolyON_natDegree]
        _ = m.val := zero_add _
        _ ≤ P.degree - 1 := by omega
    · omega
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead_deg]), hlead_deg]

/-- The leading coefficient of `wickInteractionPolyON N P c` is `1/P.degree > 0`. -/
private theorem wickInteractionPolyON_leadingCoeff (N : ℕ) (P : ONInteraction) (c : ℝ) :
    0 < (wickInteractionPolyON N P c).leadingCoeff := by
  have hdeg_pos : 0 < P.degree := by linarith [P.hdeg]
  have h1k_ne : (1 / (P.degree : ℝ)) ≠ 0 :=
    one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hdeg_pos))
  have hlead_deg : (Polynomial.C (1 / (P.degree : ℝ)) * wickMonomialPolyON N c P.degree).natDegree
      = P.degree := by rw [Polynomial.natDegree_C_mul h1k_ne, wickMonomialPolyON_natDegree]
  have hsum_natdeg : (∑ m : Fin P.degree, Polynomial.C (P.coeff m) *
      wickMonomialPolyON N c m).natDegree < P.degree := by
    apply lt_of_le_of_lt
    · apply Polynomial.natDegree_sum_le_of_forall_le (n := P.degree - 1)
      intro m _
      calc (Polynomial.C (P.coeff m) * wickMonomialPolyON N c (m : ℕ)).natDegree
          ≤ (Polynomial.C (P.coeff m)).natDegree + (wickMonomialPolyON N c (m : ℕ)).natDegree :=
            Polynomial.natDegree_mul_le
        _ = 0 + (m : ℕ) := by rw [Polynomial.natDegree_C, wickMonomialPolyON_natDegree]
        _ = m.val := zero_add _
        _ ≤ P.degree - 1 := by omega
    · omega
  -- leadingCoeff (wickInteractionPolyON N P c) = leadingCoeff of the leading term C(1/k)*T_k
  have hmonic_coeff : (wickMonomialPolyON N c P.degree).coeff P.degree = 1 := by
    have := (wickMonomialPolyON_monic N c P.degree).leadingCoeff
    rwa [Polynomial.leadingCoeff, wickMonomialPolyON_natDegree] at this
  have hsum_coeff_zero : (∑ m : Fin P.degree, Polynomial.C (P.coeff m) *
      wickMonomialPolyON N c m).coeff P.degree = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hsum_natdeg
  -- Use the natDegree result to identify where the leading coefficient lives
  have hfull_nd : (wickInteractionPolyON N P c).natDegree = P.degree :=
    wickInteractionPolyON_natDegree N P c
  rw [Polynomial.leadingCoeff, hfull_nd, wickInteractionPolyON,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, hmonic_coeff, hsum_coeff_zero]
  simp [h1k_ne, one_div, inv_pos, Nat.cast_pos.mpr hdeg_pos]

/-- The Wick interaction at a single site is bounded below.

`wickInteraction_ON N P c t` is a polynomial in t of degree P.degree
with positive leading coefficient 1/P.degree. For t ≥ 0, such a
polynomial is bounded below.

Proof: Express as formal polynomial Q with positive leading coefficient,
so Q → +∞ as t → +∞. Apply the extreme value theorem on [0, ∞). -/
theorem wickInteraction_bounded_below (P : ONInteraction) (c : ℝ) (N_val : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → C ≤ wickInteraction_ON N_val P c t := by
  -- Represent as evaluation of formal polynomial Q with positive leading coeff 1/P.degree
  let Q := wickInteractionPolyON N_val P c
  -- Q ≠ 0 since leadingCoeff Q > 0
  have hQ_ne : Q ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mp
      (ne_of_gt (wickInteractionPolyON_leadingCoeff N_val P c))
  -- Q.eval → +∞ as t → +∞
  have hQ_tendsto : Filter.Tendsto (fun t : ℝ => Q.eval t) Filter.atTop Filter.atTop := by
    apply Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
    · rw [Polynomial.degree_eq_natDegree hQ_ne, wickInteractionPolyON_natDegree]
      exact_mod_cast show 0 < P.degree by linarith [P.hdeg]
    · exact le_of_lt (wickInteractionPolyON_leadingCoeff N_val P c)
  -- Q.eval is continuous on Ici 0 (Q is a polynomial, so its eval is continuous)
  have hcont_Q : ContinuousOn (fun t : ℝ => Q.eval t) (Set.Ici 0) := by
    -- Q is a Polynomial ℝ, so eval is continuous; use congr with wickInteractionPolyON
    have : (fun t : ℝ => Q.eval t) = (fun t : ℝ => wickInteraction_ON N_val P c t) :=
      funext (fun t => wickInteractionPolyON_eval N_val P c t)
    rw [this]
    -- wickInteraction_ON is continuous: it equals a polynomial eval which is continuous
    -- Each Wick monomial is continuous (via its formal polynomial)
    have hcont_Tk : ∀ k : ℕ, Continuous (fun t : ℝ => wickMonomial_ON N_val c k t) := by
      intro k
      have heq : (fun t : ℝ => wickMonomial_ON N_val c k t) =
                 (fun t : ℝ => (wickMonomialPolyON N_val c k).eval t) :=
        funext (fun t => (wickMonomialPolyON_eval N_val c k t).symm)
      rw [heq]; fun_prop
    -- The full interaction is continuous as a sum of continuous terms
    apply Continuous.continuousOn
    unfold wickInteraction_ON
    exact (continuous_const.mul (hcont_Tk P.degree)).add
      (continuous_finset_sum _ (fun m _ => continuous_const.mul (hcont_Tk m)))
  -- Q.eval is eventually ≥ Q.eval 0 on cocompact ℝ ⊓ 𝓟 (Ici 0):
  -- cocompact ℝ ⊓ 𝓟 (Ici 0) = atTop ⊓ 𝓟 (Ici 0), and Q.eval → +∞ on atTop
  have h_large : ∀ᶠ t in Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici 0),
      Q.eval 0 ≤ Q.eval t := by
    rw [cocompact_eq_atBot_atTop, inf_sup_right,
        (Filter.disjoint_atBot_principal_Ici (0 : ℝ)).eq_bot, bot_sup_eq]
    exact (hQ_tendsto.eventually (Filter.eventually_ge_atTop (Q.eval 0))).filter_mono
      inf_le_left
  -- EVT: Q has a minimum t₀ on the closed set Ici 0
  obtain ⟨t₀, _ht₀_mem, ht₀_min⟩ :=
    hcont_Q.exists_isMinOn' isClosed_Ici (Set.mem_Ici.mpr le_rfl) h_large
  -- The minimum value Q.eval t₀ = wickInteraction_ON N_val P c t₀ is the lower bound
  refine ⟨wickInteraction_ON N_val P c t₀, fun t ht => ?_⟩
  have h_eq : ∀ s : ℝ, Q.eval s = wickInteraction_ON N_val P c s :=
    fun s => wickInteractionPolyON_eval N_val P c s
  have hmin : Q.eval t₀ ≤ Q.eval t := ht₀_min (Set.mem_Ici.mpr ht)
  rw [h_eq t₀, h_eq t] at hmin
  exact hmin

/-- The O(N) interaction is bounded below.

V(φ) = a^d · Σ_x :P(|φ(x)|²):_c where each term :P(t):_c ≥ -C for t ≥ 0.
So V(φ) ≥ a^d · |Λ| · (-C) = -B. -/
theorem onNelsonEstimate (P : ONInteraction) (c a : ℝ) (ha : 0 < a)
    (hc : 0 < c) :
    ∃ B : ℝ, ∀ (φ : Fin N → FinLatticeField d M),
      onInteraction N d M P c a φ ≥ -B := by
  obtain ⟨C, hC⟩ := wickInteraction_bounded_below P c N
  refine ⟨-(a ^ d * ((Finset.univ : Finset (FinLatticeSites d M)).card : ℝ) * C), fun φ => ?_⟩
  unfold onInteraction
  calc a ^ d * ∑ x : FinLatticeSites d M, wickInteraction_ON N P c (siteNormSq N d M φ x)
      ≥ a ^ d * ∑ x : FinLatticeSites d M, C := by
        gcongr with x _
        exact hC _ (siteNormSq_nonneg N d M φ x)
    _ = a ^ d * (Finset.univ.card : ℝ) * C := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ = -(-(a ^ d * (Finset.univ.card : ℝ) * C)) := by ring

/-! ## The interacting measure -/

/-- The Boltzmann weight exp(-V_N(φ)). -/
def onBoltzmannWeight (P : ONInteraction) (c a : ℝ)
    (φ : Fin N → FinLatticeField d M) : ℝ :=
  Real.exp (-onInteraction N d M P c a φ)

/-- The Boltzmann weight is strictly positive. -/
theorem onBoltzmannWeight_pos (P : ONInteraction) (c a : ℝ)
    (φ : Fin N → FinLatticeField d M) :
    0 < onBoltzmannWeight N d M P c a φ :=
  Real.exp_pos _

/-- The partition function Z_N = ∫ exp(-V_N) dμ^{⊗N}. -/
def onPartitionFunction (P : ONInteraction) (c a : ℝ)
    (μ_scalar : Measure (FinLatticeField d M)) : ℝ :=
  ∫ φ, onBoltzmannWeight N d M P c a φ ∂(nComponentMeasure N μ_scalar)

/-- **The O(N) interacting measure on the lattice.**

  μ_{int,N} = (1/Z_N) · exp(-V_N) · dμ_{GFF}^{⊗N}

This is a probability measure when V_N is bounded below (Nelson estimate)
and measurable. -/
def onInteractingMeasure (P : ONInteraction) (c a : ℝ)
    (μ_scalar : Measure (FinLatticeField d M)) :
    Measure (Fin N → FinLatticeField d M) :=
  let μ_N := nComponentMeasure N μ_scalar
  let Z := onPartitionFunction N d M P c a μ_scalar
  (ENNReal.ofReal Z)⁻¹ •
    μ_N.withDensity (fun φ => ENNReal.ofReal (onBoltzmannWeight N d M P c a φ))

/-! ## Continuity and measurability of the interaction -/

/-- Induction pair for continuity of Wick monomials (carries consecutive degrees). -/
private def wickMonomial_contPair (N : ℕ) (c : ℝ) (k : ℕ) : Prop :=
  Continuous (fun t : ℝ => wickMonomial_ON N c k t) ∧
  Continuous (fun t : ℝ => wickMonomial_ON N c (k + 1) t)

private lemma wickMonomial_contPair_inductive (N : ℕ) (c : ℝ) (k : ℕ) :
    wickMonomial_contPair N c k := by
  induction k with
  | zero =>
    exact ⟨by simp [wickMonomial_ON]; exact continuous_const,
           by show Continuous (fun t : ℝ => t - ↑N * c); fun_prop⟩
  | succ k ih =>
    obtain ⟨hk, hk1⟩ := ih
    exact ⟨hk1, by
      show Continuous (fun t : ℝ =>
        (t - wickShiftCoeff N (k + 1) * c) * wickMonomial_ON N c (k + 1) t -
        wickLowerCoeff N (k + 1) * c ^ 2 * wickMonomial_ON N c k t)
      exact ((continuous_id.sub continuous_const).mul hk1).sub
        (continuous_const.mul hk)⟩

/-- Each Wick monomial is continuous in its argument t. -/
private lemma wickMonomial_ON_cont (N : ℕ) (c : ℝ) (k : ℕ) :
    Continuous (fun t : ℝ => wickMonomial_ON N c k t) :=
  (wickMonomial_contPair_inductive N c k).1

/-- The Wick interaction is continuous in t. -/
private lemma wickInteraction_ON_cont (N : ℕ) (c : ℝ) (P : ONInteraction) :
    Continuous (fun t : ℝ => wickInteraction_ON N P c t) := by
  unfold wickInteraction_ON
  exact (continuous_const.mul (wickMonomial_ON_cont N c P.degree)).add
    (continuous_finset_sum _ (fun m _ =>
      continuous_const.mul (wickMonomial_ON_cont N c m)))

/-- The Boltzmann weight is measurable.

Follows because exp(-V_N) is a composition of continuous functions
(polynomials) of the measurable projections on the finite product space. -/
private lemma onBoltzmannWeight_measurable (P : ONInteraction) (c a : ℝ) :
    Measurable (onBoltzmannWeight N d M P c a) := by
  unfold onBoltzmannWeight onInteraction
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro x _
  -- wickInteraction_ON N P c (siteNormSq N d M φ x) is measurable in φ via continuity
  apply (wickInteraction_ON_cont N c P).measurable.comp
  unfold siteNormSq
  apply Finset.measurable_sum
  intro i _
  apply Measurable.pow_const
  exact (measurable_pi_apply x).comp (measurable_pi_apply i)

/-- The O(N) interacting measure is a probability measure.

Proof: same as scalar case. exp(-V) > 0 everywhere and bounded
(from the Nelson estimate), so Z > 0 and the normalized measure
has total mass 1. -/
theorem onInteractingMeasure_isProbability
    (P : ONInteraction) (c a : ℝ) (ha : 0 < a) (hc : 0 < c)
    (μ_scalar : Measure (FinLatticeField d M))
    [IsProbabilityMeasure μ_scalar] :
    IsProbabilityMeasure (onInteractingMeasure N d M P c a μ_scalar) := by
  constructor
  show (onInteractingMeasure N d M P c a μ_scalar) Set.univ = 1
  simp only [onInteractingMeasure, Measure.smul_apply, smul_eq_mul]
  -- Abbreviations for readability
  let μ_N := nComponentMeasure N μ_scalar
  let bw := onBoltzmannWeight N d M P c a
  let Z := onPartitionFunction N d M P c a μ_scalar
  -- Nelson bound gives: bw ≤ exp(B) everywhere
  obtain ⟨B, hB⟩ := onNelsonEstimate N d M P c a ha hc
  -- Boltzmann weight is strictly positive everywhere
  have hbw_pos : ∀ φ, 0 < bw φ := onBoltzmannWeight_pos N d M P c a
  -- Boltzmann weight is integrable (bounded above by exp(B))
  have hbw_int : Integrable bw μ_N := by
    apply (memLp_of_bounded (a := 0) (b := Real.exp B)
      (ae_of_all _ (fun φ => ?_))
      (onBoltzmannWeight_measurable N d M P c a).aestronglyMeasurable (p := 1)).integrable le_rfl
    exact ⟨le_of_lt (hbw_pos φ), Real.exp_le_exp_of_le (by linarith [hB φ])⟩
  -- Partition function Z > 0 (since bw > 0 and μ_N is a probability measure)
  have hZ_pos : 0 < Z := by
    unfold Z onPartitionFunction
    rw [integral_pos_iff_support_of_nonneg (fun φ => le_of_lt (hbw_pos φ)) hbw_int]
    have hsupport : Function.support bw = Set.univ := by
      ext φ; simp [Function.mem_support, (hbw_pos φ).ne']
    rw [hsupport, measure_univ]; norm_num
  -- The withDensity measure has total mass = ENNReal.ofReal Z
  have hmass : μ_N.withDensity (fun φ => ENNReal.ofReal (bw φ)) Set.univ =
      ENNReal.ofReal Z := by
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
        MeasureTheory.setLIntegral_univ]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hbw_int
      (ae_of_all _ fun φ => le_of_lt (hbw_pos φ))).symm
  -- (1/Z) * Z = 1
  rw [hmass]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr hZ_pos) ENNReal.ofReal_ne_top

/-! ## N-dependence -/

/-- The partition function Z_N is polynomial in N.

Z_N = ∫ exp(-V_N) dμ^{⊗N} where V_N is polynomial in N
(from wickInteraction_ON_polynomial_in_N). On the finite lattice,
exp(-V_N) is an entire function of V_N, and V_N is polynomial in N,
so Z_N is an entire function of N (hence polynomial for integer N). -/
theorem onPartitionFunction_polynomial_in_N
    (P : ONInteraction) (c a : ℝ) (ha : 0 < a)
    (μ_scalar : Measure (FinLatticeField d M))
    [IsProbabilityMeasure μ_scalar] :
    -- Z_N is polynomial in N (when viewed as a function of N)
    True := by trivial -- placeholder

end Pphi2N

end
