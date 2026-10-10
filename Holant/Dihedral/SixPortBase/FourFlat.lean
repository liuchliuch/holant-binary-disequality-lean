import Holant.Dihedral.SixPortBase.Sector
import Holant.Dihedral.SixToFour.FourFlat

/-! Literal four-flat support, derived from the complementary analytic
endpoints. The finite layout lemma concerns four distinct original ports only. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.SectorRuling
open Holant.Certificates.NormalizedDihedralQ6 Holant.Dihedral.CompatibleCoefficientLine
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

 private theorem source_layout : ∀ a b c d : Fin 4,List.Nodup [a,b,c,d] →
    ∃ i : Fin 3,∃ f r : Bool,
      (fixedEdge (sourceEdge (i,f))=(a.succ.succ,b.succ.succ) ∨
        fixedEdge (sourceEdge (i,f))=(b.succ.succ,a.succ.succ)) ∧
      (if r then ((varyingEdge (sourceEdge (i,f))).2,(varyingEdge (sourceEdge (i,f))).1)
        else varyingEdge (sourceEdge (i,f)))=(c.succ.succ,d.succ.succ) := by decide

 theorem layout_nodup (p : Ports) (e f : Fin 2) (hef : e ≠ f) :
    List.Nodup [p (e,false),p (e,true),p (f,false),p (f,true)] := by
  have hh : List.Nodup [(e,false),(e,true),(f,false),(f,true)] := by
    simp [hef,Ne.symm hef]
  exact hh.map p.injective

 private theorem xor_iff (a b c : Bool) : b=(a ^^ c) ↔ (a ^^ b)=c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Each arbitrary original residual matching and its chosen varying edge has
one of the atlas's literal source records, preserving both orientations. -/
 theorem sector_layout (p : Ports) (e f : Fin 2) (hef : e ≠ f) (α β r : Bool) :
    ∃ D : SixToFour.SectorData,∀ γ x,SixToFour.sectorEquations γ D x ↔
      x 1=(x 0 ^^ γ) ∧
      x (p (e,true)).succ.succ=(x (p (e,false)).succ.succ ^^ α) ∧
      x (p (f,false)).succ.succ=(r ^^ x 0) ∧
      x (p (f,true)).succ.succ=(r ^^ x 0 ^^ β) := by
  obtain ⟨i,j,v,hfixed,hvarying⟩ := source_layout _ _ _ _ (layout_nodup p e f hef)
  let D : SixToFour.SectorData := ((i,j,α,β,r),v)
  have hf : SixToFour.fixed D=fixedEdge (sourceEdge (i,j)) := by
    cases v <;> rfl
  have hv : SixToFour.varying D=(p (f,false) |>.succ.succ,p (f,true) |>.succ.succ) := by
    simpa only [D,SixToFour.varying,SixToFour.sector,sourceSectorEquiv_apply] using hvarying
  refine ⟨D,?_⟩
  intro γ x
  change (_ ∧ (x (SixToFour.fixed D).1 ^^ x (SixToFour.fixed D).2)=α ∧
      x (SixToFour.varying D).1=(r ^^ x 0) ∧
      x (SixToFour.varying D).2=(r ^^ x 0 ^^ β)) ↔ _
  rw [hf,hv]
  rcases hfixed with hfixed|hfixed <;> rw [hfixed] <;> simp only [Prod.fst,Prod.snd]
  · simp only [xor_iff]
  · rw [Bool.xor_comm (x (p (e,true)).succ.succ)]
    simp only [xor_iff]

 theorem ComplementarySector.support {m : ℕ} (hm : 0<m)
    {U V : Signature Scalar 4} (D : ComplementarySector m U V) :
    ∃ α : Bool,∀ z y,(if z then V else U) y ≠ 0 ↔
      y (D.ports (D.fixedEdge,true))=(y (D.ports (D.fixedEdge,false)) ^^ α) ∧
      y (D.ports (D.varyingEdge,false))=(D.orientation ^^ z) ∧
      y (D.ports (D.varyingEdge,true))=(D.orientation ^^ z ^^ D.parity) := by
  obtain ⟨α,w,hw,hQ⟩ := groupM_isMonomial hm D.fixed_mem
  refine ⟨α,?_⟩
  intro z y
  cases z
  · change U y ≠ 0 ↔ _
    rw [congrFun D.first_exact y]
    simp [twoProduct,hQ,monomial,scale,axis,D.first_ne_zero,hw,and_assoc,and_left_comm,and_comm]
  · change V y ≠ 0 ↔ _
    rw [congrFun D.second_exact y]
    simp [twoProduct,hQ,monomial,scale,axis,D.second_ne_zero,hw,and_assoc,and_left_comm,and_comm]

/-- A C/C pair gives exactly the source's four-flat support; no endpoint
support atlas is assumed. -/
 theorem complementary_four_flat {m : ℕ} (hm : 0<m) (h : Signature Scalar 6)
    (E : ComplementarySector m (sectorFirst (s:=2) h false) (sectorSecond (s:=2) h false))
    (O : ComplementarySector m (sectorFirst (s:=2) h true) (sectorSecond (s:=2) h true)) :
    ∃ D : SixToFour.FourFlatData,D.ports=Equiv.refl _ ∧ ∀ x,h x ≠ 0 ↔ D.Holds x := by
  obtain ⟨α,hE⟩ := E.support hm
  obtain ⟨β,hO⟩ := O.support hm
  obtain ⟨dE,hdE⟩ := sector_layout E.ports E.fixedEdge E.varyingEdge E.distinct α E.parity E.orientation
  obtain ⟨dO,hdO⟩ := sector_layout O.ports O.fixedEdge O.varyingEdge O.distinct β O.parity O.orientation
  refine ⟨⟨Equiv.refl _,dE,dO⟩,rfl,?_⟩
  intro x
  change h x ≠ 0 ↔ SixToFour.sectorEquations false dE x ∨ SixToFour.sectorEquations true dO x
  rw [hdE,hdO]
  have he := hE (x 0) (fun i => x i.succ.succ)
  have ho := hO (x 0) (fun i => x i.succ.succ)
  have hx : pair (x 0) (x 1) (fun i => x i.succ.succ)=x := pair_eta x
  cases h0 : x 0 <;> cases h1 : x 1
  all_goals
    have hx' := hx
    simp only [h0,h1] at hx'
    simp [h0,h1,sectorFirst,sectorSecond] at he ho ⊢
  all_goals first
    | simpa only [hx'] using he
    | simpa only [hx'] using ho

end Holant.Dihedral.SixPortBase
