import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli
import Conjectures.Goldbach.WideSignedRemainderBridge

-- 父目标 T n = remainder n \ inner n 的二分为两部分，两半不交且并为 T：
--   A n = T n ∩ lowWideArcs n   （落在扩宽低模裙边带内的那部分）
--   B n = T n \ lowWideArcs n  （落在扩宽低模裙边带外的那部分）
-- 两个 child 都带同一条 let 链，预算各为 floor(-e/2*n)，更强，故可独立假定。
-- 归约只用 indicator 在测集上的可加性（局部 have cutMeas / cutAdd），
-- 不调用 WideSignedRemainderBridge，避免循环引用父命题本身。

-- child 1 zh: 父目标中落入扩宽低模裙边带的部分 A n = T n ∩ lowWideArcs n 的积分实部，
--            在更强预算 floor(-e/2*n) 下有无条件单侧下界，e 任意小。
-- child 1 en: Stronger-budget floor at minus (e/2) n on the part of the parent target
--            that lies inside the widened low-modulus skirt.
-- child 2 zh: 父目标中落在扩宽低模裙边带之外的部分 B n = T n \ lowWideArcs n 的积分实部，
--            在更强预算 floor(-e/2*n) 下有无条件单侧下界，e 任意小。
-- child 2 en: Stronger-budget floor at minus (e/2) n on the part of the parent target
--            that lies outside the widened low-modulus skirt.

theorem Conjectures.Cuts.Cutd8f160af54171f1ff48cd4ab
    (h₁ : have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℕ := fun (x7 : ℕ) => ⌊(↑x7 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x8 : ℕ → ℕ := fun (x8 : ℕ) => (256 : ℕ) * x7 x8 * x4 x8; have x9 : ℕ → Set ℝ := fun (x9 : ℕ) => {x10 : ℝ | ∃ (x11 : ℕ) (x12 : ℕ), (1 : ℕ) ≤ x11 ∧ x11 ≤ x7 x9 ∧ x12 ≤ x11 ∧ x12.Coprime x11 ∧ |x10 - (↑x12 : ℝ) / (↑x11 : ℝ)| ≤ (↑(x8 x9) : ℝ) / ((↑x11 : ℝ) * (↑x9 : ℝ))}; have x10 : ℕ → Set ℝ := fun (x10 : ℕ) => {x11 : ℝ | ∃ (x12 : ℕ) (x13 : ℕ), (1 : ℕ) ≤ x12 ∧ x12 ≤ x4 x10 ∧ x13 ≤ x12 ∧ x13.Coprime x12 ∧ |x11 - (↑x13 : ℝ) / (↑x12 : ℝ)| ≤ (↑(x8 x10) : ℝ) / ((↑x12 : ℝ) * (↑x10 : ℝ))}; have x11 : ℕ → Set ℝ := fun (x11 : ℕ) => x10 x11 \ x5 x11; have x12 : ℕ → Set ℝ := fun (x12 : ℕ) => (x9 x12 \ x5 x12) \ x11 x12; have x13 : ℕ → Set ℝ := fun (x13 : ℕ) => {x14 : ℝ | ∃ (x15 : ℕ) (x16 : ℕ), (1 : ℕ) ≤ x15 ∧ x15 ≤ x7 x13 ∧ x16 ≤ x15 ∧ x16.Coprime x15 ∧ |x14 - (↑x16 : ℝ) / (↑x15 : ℝ)| ≤ (↑(x4 x13) : ℝ) * (↑x13 : ℝ) ^ (1 / 6 : ℝ) / ((↑x15 : ℝ) * (↑x13 : ℝ))}; have x14 : ℕ → Set ℝ → ℝ := fun (x14 : ℕ) (x15 : Set ℝ) => (∫ (x16 : ℝ) in (0 : ℝ)..(1 : ℝ), x15.indicator (x6 x14) x16).re; have x15 : (ℕ → Set ℝ) → Prop := fun (x15 : ℕ → Set ℝ) => ∀ (x16 : ℝ), (0 : ℝ) < x16 → ∃ (x18 : ℕ), ∀ (x19 : ℕ), x18 ≤ x19 → Even x19 → -((x16 / 2) * (↑x19 : ℝ)) ≤ x14 x19 (x15 x19); x15 fun (x16 : ℕ) => (x12 x16 \ x13 x16) ∩ x10 x16)
    (h₂ : have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℕ := fun (x7 : ℕ) => ⌊(↑x7 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x8 : ℕ → ℕ := fun (x8 : ℕ) => (256 : ℕ) * x7 x8 * x4 x8; have x9 : ℕ → Set ℝ := fun (x9 : ℕ) => {x10 : ℝ | ∃ (x11 : ℕ) (x12 : ℕ), (1 : ℕ) ≤ x11 ∧ x11 ≤ x7 x9 ∧ x12 ≤ x11 ∧ x12.Coprime x11 ∧ |x10 - (↑x12 : ℝ) / (↑x11 : ℝ)| ≤ (↑(x8 x9) : ℝ) / ((↑x11 : ℝ) * (↑x9 : ℝ))}; have x10 : ℕ → Set ℝ := fun (x10 : ℕ) => {x11 : ℝ | ∃ (x12 : ℕ) (x13 : ℕ), (1 : ℕ) ≤ x12 ∧ x12 ≤ x4 x10 ∧ x13 ≤ x12 ∧ x13.Coprime x12 ∧ |x11 - (↑x13 : ℝ) / (↑x12 : ℝ)| ≤ (↑(x8 x10) : ℝ) / ((↑x12 : ℝ) * (↑x10 : ℝ))}; have x11 : ℕ → Set ℝ := fun (x11 : ℕ) => x10 x11 \ x5 x11; have x12 : ℕ → Set ℝ := fun (x12 : ℕ) => (x9 x12 \ x5 x12) \ x11 x12; have x13 : ℕ → Set ℝ := fun (x13 : ℕ) => {x14 : ℝ | ∃ (x15 : ℕ) (x16 : ℕ), (1 : ℕ) ≤ x15 ∧ x15 ≤ x7 x13 ∧ x16 ≤ x15 ∧ x16.Coprime x15 ∧ |x14 - (↑x16 : ℝ) / (↑x15 : ℝ)| ≤ (↑(x4 x13) : ℝ) * (↑x13 : ℝ) ^ (1 / 6 : ℝ) / ((↑x15 : ℝ) * (↑x13 : ℝ))}; have x14 : ℕ → Set ℝ → ℝ := fun (x14 : ℕ) (x15 : Set ℝ) => (∫ (x16 : ℝ) in (0 : ℝ)..(1 : ℝ), x15.indicator (x6 x14) x16).re; have x15 : (ℕ → Set ℝ) → Prop := fun (x15 : ℕ → Set ℝ) => ∀ (x16 : ℝ), (0 : ℝ) < x16 → ∃ (x18 : ℕ), ∀ (x19 : ℕ), x18 ≤ x19 → Even x19 → -((x16 / 2) * (↑x19 : ℝ)) ≤ x14 x19 (x15 x19); x15 fun (x16 : ℕ) => (x12 x16 \ x13 x16) \ x10 x16) :
    have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℕ := fun (x7 : ℕ) => ⌊(↑x7 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x8 : ℕ → ℕ := fun (x8 : ℕ) => (256 : ℕ) * x7 x8 * x4 x8; have x9 : ℕ → Set ℝ := fun (x9 : ℕ) => {x10 : ℝ | ∃ (x11 : ℕ) (x12 : ℕ), (1 : ℕ) ≤ x11 ∧ x11 ≤ x7 x9 ∧ x12 ≤ x11 ∧ x12.Coprime x11 ∧ |x10 - (↑x12 : ℝ) / (↑x11 : ℝ)| ≤ (↑(x8 x9) : ℝ) / ((↑x11 : ℝ) * (↑x9 : ℝ))}; have x10 : ℕ → Set ℝ := fun (x10 : ℕ) => {x11 : ℝ | ∃ (x12 : ℕ) (x13 : ℕ), (1 : ℕ) ≤ x12 ∧ x12 ≤ x4 x10 ∧ x13 ≤ x12 ∧ x13.Coprime x12 ∧ |x11 - (↑x13 : ℝ) / (↑x12 : ℝ)| ≤ (↑(x8 x10) : ℝ) / ((↑x12 : ℝ) * (↑x10 : ℝ))}; have x11 : ℕ → Set ℝ := fun (x11 : ℕ) => x10 x11 \ x5 x11; have x12 : ℕ → Set ℝ := fun (x12 : ℕ) => (x9 x12 \ x5 x12) \ x11 x12; have x13 : ℕ → Set ℝ := fun (x13 : ℕ) => {x14 : ℝ | ∃ (x15 : ℕ) (x16 : ℕ), (1 : ℕ) ≤ x15 ∧ x15 ≤ x7 x13 ∧ x16 ≤ x15 ∧ x16.Coprime x15 ∧ |x14 - (↑x16 : ℝ) / (↑x15 : ℝ)| ≤ (↑(x4 x13) : ℝ) * (↑x13 : ℝ) ^ (1 / 6 : ℝ) / ((↑x15 : ℝ) * (↑x13 : ℝ))}; have x14 : ℕ → Set ℝ → ℝ := fun (x14 : ℕ) (x15 : Set ℝ) => (∫ (x16 : ℝ) in (0 : ℝ)..(1 : ℝ), x15.indicator (x6 x14) x16).re; have x15 : (ℕ → Set ℝ) → Prop := fun (x15 : ℕ → Set ℝ) => ∀ (x16 : ℝ), (0 : ℝ) < x16 → ∃ (x18 : ℕ), ∀ (x19 : ℕ), x18 ≤ x19 → Even x19 → -(x16 * (↑x19 : ℝ)) ≤ x14 x19 (x15 x19); x15 fun (x16 : ℕ) => x12 x16 \ x13 x16 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 e he
  obtain ⟨N₁, k₁⟩ := h₁ e he
  obtain ⟨N₂, k₂⟩ := h₂ e he
  refine ⟨max N₁ N₂, fun n hn hev => ?_⟩
  have a₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have a₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have cutMeas : ∀ (X : ℕ) (ρ n : ℝ),
      MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)} := by
    intro X ρ n
    have h : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧
          |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}
        = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q} ∩
          {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
        exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨q, a, h1, h2, h3, h4, h5⟩
    rw [h]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    refine (MeasurableSet.const _).inter ?_
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have cutAdd : ∀ (g : ℝ → ℂ), Continuous g → ∀ (P R : Set ℝ),
      MeasurableSet P → MeasurableSet R → Disjoint P R →
      (intervalIntegral (fun t => (P ∪ R).indicator g t) (0:ℝ) 1 MeasureTheory.volume).re =
        (intervalIntegral (fun t => P.indicator g t) (0:ℝ) 1 MeasureTheory.volume).re +
        (intervalIntegral (fun t => R.indicator g t) (0:ℝ) 1 MeasureTheory.volume).re := by
    intro g hg P R hP hR hd
    have hi : ∀ D : Set ℝ, MeasurableSet D →
        IntervalIntegrable (fun t => D.indicator g t) MeasureTheory.volume 0 1 := by
      intro D hD
      have h0 := hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h0 ⊢
      exact h0.indicator hD
    have hfun : (fun t => (P ∪ R).indicator g t) = fun t => P.indicator g t + R.indicator g t := by
      funext t
      rw [Set.indicator_union_of_disjoint hd]
    rw [hfun, intervalIntegral.integral_add (hi P hP) (hi R hR), Complex.add_re]
  have hcont : Continuous (x6 n) := by
    simp only [x6, x3, x2]
    fun_prop
  have mW : MeasurableSet (x9 n) := cutMeas (x7 n) (x8 n : ℝ) (n:ℝ)
  have mAr : MeasurableSet (x5 n) := cutMeas (x4 n) (x4 n : ℝ) (n:ℝ)
  have mLw : MeasurableSet (x10 n) := cutMeas (x4 n) (x8 n : ℝ) (n:ℝ)
  have mI : MeasurableSet (x13 n) :=
    cutMeas (x7 n) ((x4 n : ℝ) * (n:ℝ)^(1/6:ℝ)) (n:ℝ)
  have mLp : MeasurableSet (x11 n) := mLw.diff mAr
  have mR : MeasurableSet (x12 n) := (mW.diff mAr).diff mLp
  have mT : MeasurableSet (x12 n \ x13 n) := mR.diff mI
  have mP : MeasurableSet ((x12 n \ x13 n) ∩ x10 n) := mT.inter mLw
  have mQ : MeasurableSet ((x12 n \ x13 n) \ x10 n) := mT.diff mLw
  have e1 : x12 n \ x13 n =
      ((x12 n \ x13 n) ∩ x10 n) ∪ ((x12 n \ x13 n) \ x10 n) := by
    rw [Set.inter_union_sdiff]
  have d1 : Disjoint ((x12 n \ x13 n) ∩ x10 n) ((x12 n \ x13 n) \ x10 n) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact ht'.2 ht.2
  have key : x14 n (x12 n \ x13 n) =
      x14 n ((x12 n \ x13 n) ∩ x10 n) + x14 n ((x12 n \ x13 n) \ x10 n) := by
    have hJd : ∀ A : Set ℝ,
        x14 n A = (intervalIntegral (fun t => A.indicator (x6 n) t) (0:ℝ) 1 MeasureTheory.volume).re :=
      fun A => rfl
    rw [hJd, hJd, hJd]
    conv_lhs => rw [e1]
    rw [cutAdd (x6 n) hcont _ _ mP mQ d1]
  have b₁ : -((e/2) * (n:ℝ)) ≤ x14 n ((x12 n \ x13 n) ∩ x10 n) := k₁ n a₁ hev
  have b₂ : -((e/2) * (n:ℝ)) ≤ x14 n ((x12 n \ x13 n) \ x10 n) := k₂ n a₂ hev
  have hcoef : e/2 + e/2 = e := by ring
  linarith [key, b₁, b₂, hcoef]
