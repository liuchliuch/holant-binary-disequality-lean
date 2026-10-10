import Holant.Dihedral.SixPortBase.Unary
import Holant.Dihedral.SixPortBase.CrossingBranches

/-! The finite crossing formulas are applied to the actual analytic endpoint
coefficients. Neither a row support nor a factor witness is assumed here. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.SectorRuling
open Holant.Dihedral.CompatibleCoefficientLine Crossing
set_option backward.isDefEq.respectTransparency false

 def twoFactors (e : Fin 2) (Q A : Mat) : Fin 2 → Mat := fun i => if i=e then Q else A

 theorem twoFactors_product (p : Ports) (e f : Fin 2) (hef : e ≠ f) (Q A : Mat) :
    productValue p (twoFactors e Q A) 1=twoProduct p e f Q A := by
  funext x
  rw [show productValue p (twoFactors e Q A) 1 x=
    Holant.Certificates.MatchingContractionClosure.productValue p (twoFactors e Q A) 1 x from rfl,
    product_two p e f hef]
  simp [twoFactors,twoProduct,Ne.symm hef]

 theorem twoFactors_monomial (e : Fin 2) {Q A : Mat} (hQ : IsMonomial Q) (hA : IsMonomial A) :
    ∀ i,IsMonomial (twoFactors e Q A i) := by
  intro i
  by_cases hi : i=e <;> simp only [twoFactors,hi,ite_true,ite_false]
  · exact hQ
  · exact hA

 theorem twoFactors_point (e : Fin 2) {Q A : Mat} (hQ : IsMonomial Q) (hA : IsPoint A) :
    OnePointProduct (twoFactors e Q A) := by
  fin_cases e
  · exact Or.inl ⟨hQ,hA⟩
  · exact Or.inr ⟨hA,hQ⟩

 theorem axis_point (p r : Bool) : IsPoint (axis p r) := by
  exact ⟨r,r ^^ p,1,one_ne_zero,by funext i j; simp [axis,point]⟩

 def parityWeights (γ : Bool) (a b : Scalar) : Mat := monomial γ (fun z => if z then b else a)

 theorem parityWeights_card (γ : Bool) (a b : Scalar) :
    (binarySupport (parityWeights γ a b)).card=(if a=0 then 0 else 1)+(if b=0 then 0 else 1) := by
  classical
  have hh : binarySupport (parityWeights γ a b)=
      (if a=0 then ∅ else {(false,γ)}) ∪ (if b=0 then ∅ else {(true,!γ)}) := by
    ext x
    rcases x with ⟨i,j⟩
    by_cases ha : a=0 <;> by_cases hb : b=0 <;>
      cases γ <;> cases i <;> cases j <;> simp [parityWeights,monomial,ha,hb]
  rw [hh]
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> simp [ha,hb]

 theorem parityWeights_card_pos (γ : Bool) (a b : Scalar) (hn : a ≠ 0 ∨ b ≠ 0) :
    0 < (binarySupport (parityWeights γ a b)).card := by
  rw [parityWeights_card]
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> simp_all

 theorem parityWeights_card_le_two (γ : Bool) (a b : Scalar) :
    (binarySupport (parityWeights γ a b)).card≤2 := by
  rw [parityWeights_card]
  split_ifs <;> omega

 theorem parityWeights_singleton (γ : Bool) (a b : Scalar)
    (hc : (binarySupport (parityWeights γ a b)).card≤1) : a=0 ∨ b=0 := by
  rw [parityWeights_card] at hc
  by_cases ha : a=0
  · exact Or.inl ha
  · right
    by_contra hb
    simp [ha,hb] at hc

 theorem ProportionalSector.rows {m : ℕ} {h : Signature Scalar 6} (γ : Bool)
    (D : ProportionalSector m (sectorFirst (s:=2) h γ) (sectorSecond (s:=2) h γ))
    (a : Bool) (y : Fin 4 → Bool) :
    h (pair a (a ^^ γ) y)=
      (if a then D.second else D.first)*productValue D.ports (twoFactors D.fixedEdge D.fixed D.varying) 1 y := by
  rw [twoFactors_product D.ports D.fixedEdge D.varyingEdge D.distinct]
  cases a
  · simpa [sectorFirst] using congrFun D.first_exact y
  · simpa [sectorSecond] using congrFun D.second_exact y

 theorem ComplementarySector.rows {m : ℕ} {h : Signature Scalar 6} (γ : Bool)
    (D : ComplementarySector m (sectorFirst (s:=2) h γ) (sectorSecond (s:=2) h γ))
    (a : Bool) (y : Fin 4 → Bool) :
    h (pair a (a ^^ γ) y)=
      (if a then D.second else D.first)*productValue D.ports
        (twoFactors D.fixedEdge D.fixed (axis D.parity (D.orientation ^^ a))) 1 y := by
  rw [twoFactors_product D.ports D.fixedEdge D.varyingEdge D.distinct]
  cases a
  · have hh := congrFun D.first_exact y
    change h (pair false γ y)=_ at hh
    simp only [Bool.false_xor,Bool.false_eq_true,ite_false,Bool.xor_false]
    rw [hh]
    simp only [twoProduct,scale]
    ring
  · have hh := congrFun D.second_exact y
    change h (pair true (!γ) y)=_ at hh
    rw [show (true ^^ γ)=(!γ) by cases γ <;> rfl,hh]
    simp only [twoProduct,scale,Bool.xor_true,ite_true]
    ring

 theorem pp_rows {m : ℕ} (h : Signature Scalar 6)
    (E : ProportionalSector m (sectorFirst (s:=2) h false) (sectorSecond (s:=2) h false))
    (O : ProportionalSector m (sectorFirst (s:=2) h true) (sectorSecond (s:=2) h true)) :
    (fun w : PairWord => fun y => h (pair w.1 w.2 y))=
      sourceRows (parityWeights false E.first E.second) (parityWeights true O.first O.second)
        (fun _ => productValue E.ports (twoFactors E.fixedEdge E.fixed E.varying) 1)
        (fun _ => productValue O.ports (twoFactors O.fixedEdge O.fixed O.varying) 1) := by
  funext w y
  rcases w with ⟨a,b⟩
  have hE := E.rows false a y
  have hO := O.rows true a y
  cases a <;> cases b
  all_goals first
    | simpa [sourceRows,parityWeights,monomial] using hE
    | simpa [sourceRows,parityWeights,monomial] using hO

 theorem pc_rows {m : ℕ} (h : Signature Scalar 6) (γ : Bool)
    (E : ProportionalSector m (sectorFirst (s:=2) h γ) (sectorSecond (s:=2) h γ))
    (O : ComplementarySector m (sectorFirst (s:=2) h (!γ)) (sectorSecond (s:=2) h (!γ))) :
    (fun w : PairWord => fun y => h (pair w.1 w.2 y))=
      sourceRows (parityWeights γ E.first E.second) (parityWeights (!γ) O.first O.second)
        (fun _ => productValue E.ports (twoFactors E.fixedEdge E.fixed E.varying) 1)
        (fun w => productValue O.ports
          (twoFactors O.fixedEdge O.fixed (axis O.parity (O.orientation ^^ w.1))) 1) := by
  funext w y
  rcases w with ⟨a,b⟩
  have hE := E.rows γ a y
  have hO := O.rows (!γ) a y
  cases γ <;> cases a <;> cases b
  all_goals first
    | simpa [sourceRows,parityWeights,monomial] using hE
    | simpa [sourceRows,parityWeights,monomial] using hO

end Holant.Dihedral.SixPortBase
