/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.IsonormalGaussian

/-! Construction of a real pre-Brownian motion from an isonormal family on `L²(ℝ)`. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology lp

namespace Solution

abbrev BrownianTimeHilbert := Lp ℝ 2 (volume : Measure ℝ)

def brownianTimeVector (t : ℝ≥0) : BrownianTimeHilbert :=
  indicatorConstLp (μ := volume) (s := Ioc (0 : ℝ) t) 2 measurableSet_Ioc
    (by simp only [Real.volume_Ioc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]) (1 : ℝ)

theorem brownianTimeVector_inner (s t : ℝ≥0) :
    inner ℝ (brownianTimeVector s) (brownianTimeVector t) = min (s : ℝ) t := by
  rw [brownianTimeVector, brownianTimeVector,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one _ _
      (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioc])]
  simp [Ioc_inter_Ioc]

def BrownianGaussianIndex : Type := (exists_hilbertBasis ℝ BrownianTimeHilbert).choose

def brownianTimeBasis : HilbertBasis BrownianGaussianIndex ℝ BrownianTimeHilbert :=
  (exists_hilbertBasis ℝ BrownianTimeHilbert).choose_spec.choose

def brownianCoordinateMeasure : Measure (BrownianGaussianIndex → ℝ) :=
  gaussianProductMeasure BrownianGaussianIndex

instance brownianCoordinateMeasure_isProbability : IsProbabilityMeasure brownianCoordinateMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianProductMeasure BrownianGaussianIndex))

def preBrownianPath (t : ℝ≥0) (ω : BrownianGaussianIndex → ℝ) : ℝ :=
  isonormalMap brownianTimeBasis (brownianTimeVector t) ω

theorem preBrownianPath_isPreBrownianReal :
    IsPreBrownianReal preBrownianPath brownianCoordinateMeasure := by
  apply IsGaussianProcess.isPreBrownianReal_of_covariance
    (isonormalMap_isGaussianProcess brownianTimeBasis brownianTimeVector)
  · exact fun t ↦ isonormalMap_integral brownianTimeBasis (brownianTimeVector t)
  · intro s t hst
    exact (isonormalMap_covariance brownianTimeBasis _ _).trans
      ((brownianTimeVector_inner s t).trans (min_eq_left (by exact_mod_cast hst)))

end Solution
