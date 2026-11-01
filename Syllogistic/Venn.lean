import Syllogistic.Semantics

/-!
# Venn diagrams as a decision procedure

Three overlapping circles S, M, P cut the plane into 8 regions. For questions
about three terms, the only thing a model can tell us is *which regions are
inhabited*. So there are only 2⁸ = 256 essentially different models.

This file proves that metatheorem: a syllogism is valid in *all* models
(of any size, over any type) iff it is valid in all 256 Venn models
(`valid_iff_vennValid`). Since the latter is a finite Boolean computation,
the kernel can decide validity of every syllogism by evaluation.
-/

namespace Syllogistic

/-- A region of the diagram: (inside S?, inside M?, inside P?). -/
abbrev Region := Bool × Bool × Bool

def Region.mem : Term → Region → Bool
  | .S, (s, _, _) => s
  | .M, (_, m, _) => m
  | .P, (_, _, p) => p

def allRegions : List Region :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
   (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

theorem mem_allRegions (r : Region) : r ∈ allRegions := by
  obtain ⟨a, b, c⟩ := r
  cases a <;> cases b <;> cases c <;> decide

/-- A Venn model: which regions are inhabited. -/
abbrev Venn := Region → Bool

namespace Venn
variable (R : Venn)

def holds : Cat → Bool
  | ⟨.A, s, p⟩ => allRegions.all fun r => !(R r && r.mem s && !r.mem p)
  | ⟨.E, s, p⟩ => allRegions.all fun r => !(R r && r.mem s && r.mem p)
  | ⟨.I, s, p⟩ => allRegions.any fun r => R r && r.mem s && r.mem p
  | ⟨.O, s, p⟩ => allRegions.any fun r => R r && r.mem s && !r.mem p

def inhabited : Bool :=
  [Term.S, .M, .P].all fun t => allRegions.any fun r => R r && r.mem t

/-- `R` is a counter-example to `σ`: premises true, conclusion false. -/
def counter (ei : Bool) (σ : Syllogism) : Bool :=
  (!ei || R.inhabited) && R.holds σ.major && R.holds σ.minor && !R.holds σ.concl

end Venn

/-! ## Enumerating the 256 Venn models -/

def mkVenn (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Venn
  | (false, false, false) => b0 | (false, false, true) => b1
  | (false, true, false) => b2  | (false, true, true) => b3
  | (true, false, false) => b4  | (true, false, true) => b5
  | (true, true, false) => b6   | (true, true, true) => b7

theorem mkVenn_eta (R : Venn) :
    mkVenn (R (false, false, false)) (R (false, false, true)) (R (false, true, false))
      (R (false, true, true)) (R (true, false, false)) (R (true, false, true))
      (R (true, true, false)) (R (true, true, true)) = R := by
  funext ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

def allB (k : Bool → Bool) : Bool := k false && k true

theorem allB_eq_true {k : Bool → Bool} : allB k = true ↔ ∀ b, k b = true := by
  constructor
  · intro h b; simp only [allB, Bool.and_eq_true] at h; cases b <;> simp [h]
  · intro h; simp [allB, h]

/-- Check a Boolean property of all 256 Venn models. -/
def checkAll (P : Venn → Bool) : Bool :=
  allB fun b0 => allB fun b1 => allB fun b2 => allB fun b3 =>
  allB fun b4 => allB fun b5 => allB fun b6 => allB fun b7 =>
  P (mkVenn b0 b1 b2 b3 b4 b5 b6 b7)

theorem checkAll_eq_true {P : Venn → Bool} : checkAll P = true ↔ ∀ R, P R = true := by
  constructor
  · intro h R
    rw [← mkVenn_eta R]
    simp only [checkAll, allB_eq_true] at h
    exact h _ _ _ _ _ _ _ _
  · intro h
    simp only [checkAll, allB_eq_true]
    intros
    exact h _

/-- The decision procedure. -/
def vennValid (ei : Bool) (σ : Syllogism) : Bool :=
  checkAll fun R => !(R.counter ei σ)

/-! ## The metatheorem -/

section Image
variable {U : Type} (m : Model U) (f : U → Region) (R : Venn)
  (hext : ∀ t x, m.ext t x ↔ (f x).mem t = true)
  (hR : ∀ r, R r = true ↔ ∃ x, f x = r)
include hext hR

/-- If `R` records exactly the regions hit by `m`, then `m` and `R` agree on
every categorical proposition. -/
theorem holds_iff_venn (c : Cat) : m.holds c ↔ R.holds c = true := by
  obtain ⟨form, s, p⟩ := c
  cases form <;> simp only [Model.holds, Venn.holds, List.all_eq_true, List.any_eq_true,
    Bool.and_eq_false_imp, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.not_false]
  · constructor
    · rintro h r _ ⟨hr, hs⟩
      obtain ⟨x, rfl⟩ := (hR r).1 hr
      exact (hext p x).1 (h x ((hext s x).2 hs))
    · intro h x hs
      exact (hext p x).2 (h (f x) (mem_allRegions _) ⟨(hR _).2 ⟨x, rfl⟩, (hext s x).1 hs⟩)
  · constructor
    · rintro h r _ ⟨hr, hs⟩
      obtain ⟨x, rfl⟩ := (hR r).1 hr
      cases hp : (f x).mem p
      · rfl
      · exact absurd ((hext p x).2 hp) (h x ((hext s x).2 hs))
    · intro h x hs hp
      have := h (f x) (mem_allRegions _) ⟨(hR _).2 ⟨x, rfl⟩, (hext s x).1 hs⟩
      rw [(hext p x).1 hp] at this
      cases this
  · constructor
    · rintro ⟨x, hs, hp⟩
      exact ⟨f x, mem_allRegions _, ⟨(hR _).2 ⟨x, rfl⟩, (hext s x).1 hs⟩, (hext p x).1 hp⟩
    · rintro ⟨r, _, ⟨hr, hs⟩, hp⟩
      obtain ⟨x, rfl⟩ := (hR r).1 hr
      exact ⟨x, (hext s x).2 hs, (hext p x).2 hp⟩
  · constructor
    · rintro ⟨x, hs, hp⟩
      refine ⟨f x, mem_allRegions _, ⟨(hR _).2 ⟨x, rfl⟩, (hext s x).1 hs⟩, ?_⟩
      cases h : (f x).mem p
      · rfl
      · exact absurd ((hext p x).2 h) hp
    · rintro ⟨r, _, ⟨hr, hs⟩, hp⟩
      obtain ⟨x, rfl⟩ := (hR r).1 hr
      refine ⟨x, (hext s x).2 hs, fun h => ?_⟩
      rw [(hext p x).1 h] at hp
      cases hp

theorem inhabited_iff_venn : m.Inhabited ↔ R.inhabited = true := by
  have key : ∀ t, (∃ x, m.ext t x) ↔ (allRegions.any fun r => R r && r.mem t) = true := by
    intro t
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨f x, mem_allRegions _, (hR _).2 ⟨x, rfl⟩, (hext t x).1 hx⟩
    · rintro ⟨r, _, hr, ht⟩
      obtain ⟨x, rfl⟩ := (hR r).1 hr
      exact ⟨x, (hext t x).2 ht⟩
  simp only [Model.Inhabited, Venn.inhabited, List.all_eq_true]
  constructor
  · intro h t _; exact (key t).1 (h t)
  · intro h t
    exact (key t).2 (h t (by cases t <;> simp))

end Image

/-- The model whose elements are the inhabited regions of `R`. -/
def Venn.toModel (R : Venn) : Model {r // R r = true} :=
  ⟨fun t x => x.val.mem t = true⟩

/-- **Metatheorem.** Validity over all models ⇔ validity over the 256 Venn models. -/
theorem valid_iff_vennValid (ei : Bool) (σ : Syllogism) :
    Valid ei σ ↔ vennValid ei σ = true := by
  constructor
  · intro hv
    rw [vennValid, checkAll_eq_true]
    intro R
    cases hc : R.counter ei σ
    · rfl
    · exfalso
      simp only [Venn.counter, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      obtain ⟨⟨⟨hinh, hmaj⟩, hmin⟩, hcon⟩ := hc
      have hext : ∀ t (x : {r // R r = true}), R.toModel.ext t x ↔ x.val.mem t = true :=
        fun _ _ => Iff.rfl
      have hR : ∀ r, R r = true ↔ ∃ x : {r // R r = true}, x.val = r :=
        fun r => ⟨fun h => ⟨⟨r, h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.property⟩
      have H := holds_iff_venn R.toModel Subtype.val R hext hR
      have hc := hv _ R.toModel
        (fun hei => (inhabited_iff_venn R.toModel Subtype.val R hext hR).2
          (by cases hinh with
              | inl h => rw [hei] at h; cases h
              | inr h => exact h))
        ((H _).2 hmaj) ((H _).2 hmin)
      rw [H] at hc
      rw [hc] at hcon
      cases hcon
  · intro hc U m hinh hmaj hmin
    classical
    let f : U → Region := fun x => (decide (m.ext .S x), decide (m.ext .M x), decide (m.ext .P x))
    let R : Venn := fun r => decide (∃ x, f x = r)
    have hext : ∀ t x, m.ext t x ↔ (f x).mem t = true := by
      intro t x; cases t <;> simp [f, Region.mem]
    have hR : ∀ r, R r = true ↔ ∃ x, f x = r := by intro r; simp [R]
    have H := holds_iff_venn m f R hext hR
    rw [vennValid, checkAll_eq_true] at hc
    have hR' := hc R
    have hI : (!ei || R.inhabited) = true := by
      cases ei with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_or]
        exact (inhabited_iff_venn m f R hext hR).1 (hinh rfl)
    have h1 := (H _).1 hmaj
    have h2 := (H _).1 hmin
    rw [H]
    cases h3 : R.holds σ.concl
    · simp [Venn.counter, hI, h1, h2, h3] at hR'
    · rfl

/-- Validity is decidable — by the metatheorem, via Venn diagrams. -/
instance (ei : Bool) (σ : Syllogism) : Decidable (Valid ei σ) :=
  decidable_of_iff _ (valid_iff_vennValid ei σ).symm

end Syllogistic
