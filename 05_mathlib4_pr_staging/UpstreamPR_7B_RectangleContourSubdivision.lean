/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Ring

/-!
# Four-Segment Complex Rectangle Contour Integral and Boundary Subdivisions

This module defines the concrete 4-segment oriented boundary integral `rectBoundaryIntegral`
around `[σ₁, σ₂] × [t₁, t₂]` using 1D `intervalIntegral`s and proves exact horizontal and
vertical subdivision additivity for continuous functions:

* `rectBoundaryIntegral`: 4-segment boundary integral around `[σ₁, σ₂] × [t₁, t₂]`.
* `rectBoundaryIntegral_const`: vanishing around any rectangle for constant functions.
* `rectBoundaryIntegral_split_sigma`: horizontal subdivision at any intermediate abscissa `σₘ`,
  with exact cancellation of the shared vertical edge.
* `rectBoundaryIntegral_split_height`: vertical subdivision at any intermediate height `tₘ`,
  with exact cancellation of the shared horizontal edge.
-/

@[expose] public section

open MeasureTheory Complex

/-- Oriented 4-segment complex boundary integral of `f` around `[σ₁, σ₂] × [t₁, t₂]`. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (σ₁ σ₂ t₁ t₂ : ℝ) : ℂ :=
  (∫ σ in σ₁..σ₂, f (↑σ + ↑t₁ * Complex.I)) +
  Complex.I * (∫ t in t₁..t₂, f (↑σ₂ + ↑t * Complex.I)) -
  (∫ σ in σ₁..σ₂, f (↑σ + ↑t₂ * Complex.I)) -
  Complex.I * (∫ t in t₁..t₂, f (↑σ₁ + ↑t * Complex.I))

private lemma intervalIntegrable_rect_horiz (f : ℂ → ℂ) (hf : Continuous f) (t a b : ℝ) :
    IntervalIntegrable (fun σ : ℝ => f (↑σ + ↑t * Complex.I)) volume a b :=
  (hf.comp (Complex.continuous_ofReal.add continuous_const)).intervalIntegrable a b

private lemma intervalIntegrable_rect_vert (f : ℂ → ℂ) (hf : Continuous f) (σ a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => f (↑σ + ↑t * Complex.I)) volume a b :=
  (hf.comp (continuous_const.add
    (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable a b

/-- Constant functions have vanishing rectangle boundary integral. -/
theorem rectBoundaryIntegral_const (c : ℂ) (σ₁ σ₂ t₁ t₂ : ℝ) :
    rectBoundaryIntegral (fun _ => c) σ₁ σ₂ t₁ t₂ = 0 := by
  unfold rectBoundaryIntegral
  simp only [intervalIntegral.integral_const]
  ring

/-- Horizontal rectangle subdivision: splitting `[σ₁, σ₂] × [t₁, t₂]` at `σₘ`
cancels the shared vertical segment at `σₘ` identically for any continuous `f`. -/
theorem rectBoundaryIntegral_split_sigma (f : ℂ → ℂ) (hf : Continuous f)
    (σ₁ σₘ σ₂ t₁ t₂ : ℝ) :
    rectBoundaryIntegral f σ₁ σₘ t₁ t₂ + rectBoundaryIntegral f σₘ σ₂ t₁ t₂ =
      rectBoundaryIntegral f σ₁ σ₂ t₁ t₂ := by
  have hb : (∫ σ in σ₁..σₘ, f (↑σ + ↑t₁ * Complex.I)) +
      (∫ σ in σₘ..σ₂, f (↑σ + ↑t₁ * Complex.I)) =
      ∫ σ in σ₁..σ₂, f (↑σ + ↑t₁ * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rect_horiz f hf t₁ σ₁ σₘ)
      (intervalIntegrable_rect_horiz f hf t₁ σₘ σ₂)
  have ht : (∫ σ in σ₁..σₘ, f (↑σ + ↑t₂ * Complex.I)) +
      (∫ σ in σₘ..σ₂, f (↑σ + ↑t₂ * Complex.I)) =
      ∫ σ in σ₁..σ₂, f (↑σ + ↑t₂ * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rect_horiz f hf t₂ σ₁ σₘ)
      (intervalIntegrable_rect_horiz f hf t₂ σₘ σ₂)
  unfold rectBoundaryIntegral
  rw [← hb, ← ht]
  ring

/-- Vertical rectangle subdivision: splitting `[σ₁, σ₂] × [t₁, t₂]` at any height `tₘ`
cancels the shared horizontal segment at `tₘ` identically for any continuous `f`. -/
theorem rectBoundaryIntegral_split_height (f : ℂ → ℂ) (hf : Continuous f)
    (σ₁ σ₂ t₁ tₘ t₂ : ℝ) :
    rectBoundaryIntegral f σ₁ σ₂ t₁ tₘ + rectBoundaryIntegral f σ₁ σ₂ tₘ t₂ =
      rectBoundaryIntegral f σ₁ σ₂ t₁ t₂ := by
  have hr : (∫ t in t₁..tₘ, f (↑σ₂ + ↑t * Complex.I)) +
      (∫ t in tₘ..t₂, f (↑σ₂ + ↑t * Complex.I)) =
      ∫ t in t₁..t₂, f (↑σ₂ + ↑t * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rect_vert f hf σ₂ t₁ tₘ)
      (intervalIntegrable_rect_vert f hf σ₂ tₘ t₂)
  have hl : (∫ t in t₁..tₘ, f (↑σ₁ + ↑t * Complex.I)) +
      (∫ t in tₘ..t₂, f (↑σ₁ + ↑t * Complex.I)) =
      ∫ t in t₁..t₂, f (↑σ₁ + ↑t * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rect_vert f hf σ₁ t₁ tₘ)
      (intervalIntegrable_rect_vert f hf σ₁ tₘ t₂)
  unfold rectBoundaryIntegral
  rw [← hr, ← hl]
  ring

/-- Degenerate zero-width rectangles have vanishing boundary integral. -/
theorem rectBoundaryIntegral_self_sigma (f : ℂ → ℂ) (σ t₁ t₂ : ℝ) :
    rectBoundaryIntegral f σ σ t₁ t₂ = 0 := by
  unfold rectBoundaryIntegral
  simp

/-- Degenerate zero-height rectangles have vanishing boundary integral. -/
theorem rectBoundaryIntegral_self_height (f : ℂ → ℂ) (σ₁ σ₂ t : ℝ) :
    rectBoundaryIntegral f σ₁ σ₂ t t = 0 := by
  unfold rectBoundaryIntegral
  simp
