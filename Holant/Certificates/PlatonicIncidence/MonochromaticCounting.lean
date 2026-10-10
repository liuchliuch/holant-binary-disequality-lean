import Holant.Certificates.RainbowOrbit.Deck

/-! The multiplicity of ordered matching rulings. No line geometry is assumed
by this combinatorial counting argument. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev MatchingIndex (ι : Type*) := Fin 3 × ι × ι
abbrev RulingParameter (ι : Type*) := Fin 3 × Bool × ι × Finset ι

/-- `true` varies the first ordered factor, `false` the second. -/
def rulingSet {ι : Type*} [DecidableEq ι] (r : Fin 3) (b : Bool) (f : ι)
    (L : Finset ι) : Finset (MatchingIndex ι) :=
  if b then L.image (fun i => (r,i,f)) else L.image (fun i => (r,f,i))

@[simp] theorem mem_rulingSet {ι : Type*} [DecidableEq ι]
    (r : Fin 3) (b : Bool) (f : ι) (L : Finset ι) (x : MatchingIndex ι) :
    x∈rulingSet r b f L ↔ x.1=r ∧
      if b then x.2.2=f ∧ x.2.1∈L else x.2.1=f ∧ x.2.2∈L := by
  rcases x with ⟨s,i,j⟩
  cases b <;> simp [rulingSet,Prod.ext_iff,and_comm,and_left_comm,and_assoc,eq_comm]

@[simp] theorem rulingSet_card {ι : Type*} [DecidableEq ι]
    (r : Fin 3) (b : Bool) (f : ι) (L : Finset ι) :
    (rulingSet r b f L).card=L.card := by
  cases b
  · simp only [rulingSet,Bool.false_eq_true,↓reduceIte]
    apply Finset.card_image_of_injective
    intro i j h
    exact congrArg (fun x => x.2.2) h
  · simp only [rulingSet,↓reduceIte]
    apply Finset.card_image_of_injective
    intro i j h
    exact congrArg (fun x => x.2.1) h

/-- Distinct ordered rulings with at least two domain points remain distinct
as complete sets of labeled matching products. -/
theorem rulingSet_injective {ι : Type*} [DecidableEq ι]
    (r s : Fin 3) (b c : Bool) (f g : ι) (L M : Finset ι)
    (hL : 2≤L.card) (hM : 2≤M.card)
    (he : rulingSet r b f L=rulingSet s c g M) :
    r=s ∧ b=c ∧ f=g ∧ L=M := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1<L.card)
  have hh (k : ι) : (if b then (r,k,f) else (r,f,k))∈rulingSet r b f L ↔ k∈L := by
    cases b <;> simp
  have hhi := (hh i).mpr hi
  have hhj := (hh j).mpr hj
  rw [he] at hhi hhj
  cases b <;> cases c
  · simp only [mem_rulingSet,Bool.false_eq_true,↓reduceIte] at hhi hhj
    refine ⟨hhi.1,rfl,hhi.2.1,?_⟩
    rw [←hhi.1,←hhi.2.1] at he
    ext k
    have hk := congrArg (fun A => (r,f,k)∈A) he
    simpa using hk
  · simp only [mem_rulingSet,Bool.false_eq_true,↓reduceIte] at hhi hhj
    exact False.elim (hij (hhi.2.1.trans hhj.2.1.symm))
  · simp only [mem_rulingSet,Bool.false_eq_true,↓reduceIte] at hhi hhj
    exact False.elim (hij (hhi.2.1.trans hhj.2.1.symm))
  · simp only [mem_rulingSet,↓reduceIte] at hhi hhj
    refine ⟨hhi.1,rfl,hhi.2.1,?_⟩
    rw [←hhi.1,←hhi.2.1] at he
    ext k
    have hk := congrArg (fun A => (r,k,f)∈A) he
    simpa using hk

def rulingParameters {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset (Finset ι)) : Finset (RulingParameter ι) :=
  Finset.univ.product (Finset.univ.product (Finset.univ.product D))

def rulingMap {ι : Type*} [DecidableEq ι] (p : RulingParameter ι) : Finset (MatchingIndex ι) :=
  rulingSet p.1 p.2.1 p.2.2.1 p.2.2.2

/-- All three matching labels, both ordered factor choices, and every fixed
factor for each supplied domain line. -/
def monochromaticLines {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset (Finset ι)) : Finset (Finset (MatchingIndex ι)) :=
  (rulingParameters D).image rulingMap

theorem monochromaticLines_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset (Finset ι)) (hD : ∀ L∈D,2≤L.card) :
    (monochromaticLines D).card=6*Fintype.card ι*D.card := by
  have hinj : Set.InjOn (@rulingMap ι _) (rulingParameters D) := by
    rintro ⟨r,b,f,L⟩ hp ⟨s,c,g,M⟩ hq he
    have hL : L∈D := by simpa [rulingParameters] using hp
    have hM : M∈D := by simpa [rulingParameters] using hq
    obtain ⟨hrs,hbc,hfg,hLM⟩ := rulingSet_injective r s b c f g L M
      (hD L hL) (hD M hM) he
    subst s; subst c; subst g; subst M
    rfl
  rw [monochromaticLines,Finset.card_image_iff.mpr hinj]
  simp [rulingParameters,Nat.mul_assoc]
  omega

theorem monochromaticLines_filter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset (Finset ι)) (n : ℕ) :
    (monochromaticLines D).filter (fun L => L.card=n)=
      monochromaticLines (D.filter (fun L => L.card=n)) := by
  ext S
  simp only [monochromaticLines,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨r,b,f,L⟩,hp,rfl⟩,hc⟩
    refine ⟨(r,b,f,L),?_,rfl⟩
    simpa [rulingParameters,rulingMap] using And.intro (by simpa [rulingParameters] using hp : L∈D) hc
  · rintro ⟨⟨r,b,f,L⟩,hp,rfl⟩
    have hh : L∈D ∧ L.card=n := by simpa [rulingParameters] using hp
    exact ⟨⟨(r,b,f,L),by simpa [rulingParameters] using hh.1,rfl⟩,
      by simpa [rulingMap] using hh.2⟩

theorem monochromaticLines_filter_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset (Finset ι)) (hD : ∀ L∈D,2≤L.card) (n : ℕ) :
    ((monochromaticLines D).filter (fun L => L.card=n)).card=
      6*Fintype.card ι*(D.filter (fun L => L.card=n)).card := by
  rw [monochromaticLines_filter]
  exact monochromaticLines_card _ (fun L hL => hD L (Finset.mem_filter.mp hL).1)

end
end Holant.Certificates.PlatonicIncidence
