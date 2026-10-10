import Holant.Dihedral.SixPortBase.Binary

/-! Exact common-factor extraction from the proved sampled ruling. The
normalization is evaluation at a nonzero original entry of the fixed factor,
so one fixed scalar is used for the entire analytic pencil. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Certificates Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.SectorRuling
set_option backward.isDefEq.respectTransparency false

abbrev Ports := (Fin 2 × Bool) ≃ Fin 4

def twoProduct (p : Ports) (e f : Fin 2) (Q A : Mat) : Signature Scalar 4 :=
  fun x => Q (x (p (e,false))) (x (p (e,true))) * A (x (p (f,false))) (x (p (f,true)))

def packed (p : Ports) (e : Fin 2) (a b c d : Bool) : Fin 4 → Bool :=
  fun i => if (p.symm i).1=e then (if (p.symm i).2 then b else a)
    else (if (p.symm i).2 then d else c)

 theorem product_two (p : Ports) (e f : Fin 2) (hef : e ≠ f)
    (A : Fin 2 → Mat) (κ : Scalar) (x : Fin 4 → Bool) :
    MatchingContractionClosure.productValue p A κ x=
      κ*A e (x (p (e,false))) (x (p (e,true)))*A f (x (p (f,false))) (x (p (f,true))) := by
  fin_cases e <;> fin_cases f <;> simp_all [MatchingContractionClosure.productValue,Fin.prod_univ_succ] <;> ring

 def extract (p : Ports) (e : Fin 2) (Q : Mat) (β : Bool) (q : Signature Scalar 4) : Mat :=
  fun a b => q (packed p e false β a b)/Q false β

 theorem extract_twoProduct (p : Ports) (e f : Fin 2) (hef : e ≠ f) (Q A : Mat)
    (β : Bool) (hQ : Q false β ≠ 0) : extract p e Q β (twoProduct p e f Q A)=A := by
  funext a b
  simp [extract,twoProduct,packed,Ne.symm hef,hQ]

 theorem extract_pencil (p : Ports) (e : Fin 2) (Q : Mat) (β : Bool)
    (U V : Signature Scalar 4) (t : Scalar) :
    extract p e Q β (tensorPencil U V t)=matrixPencil (extract p e Q β U) (extract p e Q β V) t := by
  funext a b
  simp only [extract,tensorPencil,matrixPencil]
  ring

 theorem extracted_product (p : Ports) (e f : Fin 2) (hef : e ≠ f)
    (A : Fin 2 → Mat) (κ c : Scalar) (Q : Mat) (β : Bool)
    (hQ : Q false β ≠ 0) (he : A e=scale c Q) :
    extract p e Q β (MatchingContractionClosure.productValue p A κ)=scale (κ*c) (A f) ∧
    MatchingContractionClosure.productValue p A κ=
      twoProduct p e f Q (extract p e Q β (MatchingContractionClosure.productValue p A κ)) := by
  have hx : MatchingContractionClosure.productValue p A κ=twoProduct p e f Q (scale (κ*c) (A f)) := by
    funext x
    rw [product_two p e f hef,he]
    simp only [twoProduct,scale]
    ring
  rw [hx,extract_twoProduct p e f hef Q _ β hQ]
  exact ⟨rfl,rfl⟩

/-- One exact original-port factor for both analytic endpoints. Sample group
membership is proved for the extracted literal matrix pencil. -/
structure ExactPencil (m : ℕ) (U V : Signature Scalar 4) where
  ports : Ports
  fixedEdge : Fin 2
  varyingEdge : Fin 2
  distinct : fixedEdge ≠ varyingEdge
  fixed : Mat
  fixed_mem : fixed ∈ groupM m
  first : Mat
  second : Mat
  first_exact : U=twoProduct ports fixedEdge varyingEdge fixed first
  second_exact : V=twoProduct ports fixedEdge varyingEdge fixed second
  samples : ∀ t,Roots m t → matrixPencil first second t=0 ∨ matrixPencil first second t ∈ groupM m

 theorem exact_pencil {m : ℕ} (hm : 3≤m) (U V : Signature Scalar 4)
    (hs : ∀ t,Roots m t → tensorPencil U V t=0 ∨ MatchingSample m 2 (tensorPencil U V t)) :
    Nonempty (ExactPencil m U V) := by
  classical
  obtain ⟨D⟩ := source_sector_ruling (s:=2) hm U V hs
  obtain ⟨e,f,hef,he⟩ : ∃ e f : Fin 2,e ≠ f ∧ D.varying ≠ some e := by
    cases hh : D.varying with
    | none => exact ⟨0,1,by decide,by simp [hh]⟩
    | some j =>
      fin_cases j
      · exact ⟨1,0,by decide,by simp [hh]⟩
      · exact ⟨0,1,by decide,by simp [hh]⟩
  let Q := D.fixed e
  obtain ⟨β,w,hw,hQ⟩ := groupM_isMonomial (by omega : 0<m) (D.fixed_mem e)
  have hQβ : Q false β ≠ 0 := by
    change D.fixed e false β ≠ 0
    rw [hQ]
    simp [monomial,hw]
  let A := extract D.ports e Q β U
  let B := extract D.ports e Q β V
  have sample (t : Scalar) (ht : Roots m t) :
      matrixPencil A B t=0 ∨ matrixPencil A B t ∈ groupM m := by
    rw [←extract_pencil]
    rcases D.samples t ht with hz|⟨C,κ,hC,hκ,hq,hline⟩
    · left
      rw [hz]
      funext a b
      simp [extract]
    · right
      obtain ⟨c,hc,heq⟩ := hline e he
      rw [hq,(extracted_product D.ports e f hef C κ c Q β hQβ heq).1]
      exact (groupM_is_group (by omega)).scale_mem _ (hC f) _ (mul_ne_zero hκ hc)
  have identities (t : Scalar) (ht : Roots m t) :
      tensorPencil U V t=twoProduct D.ports e f Q (matrixPencil A B t) := by
    rw [←extract_pencil]
    rcases D.samples t ht with hz|⟨C,κ,hC,hκ,hq,hline⟩
    · rw [hz]
      funext x
      simp [twoProduct,extract]
    · obtain ⟨c,hc,heq⟩ := hline e he
      rw [hq]
      exact (extracted_product D.ports e f hef C κ c Q β hQβ heq).2
  obtain ⟨t,ht,ht1,_⟩ := third_root hm 1 1 (Roots.one m) (Roots.one m)
  have hAB : U=twoProduct D.ports e f Q A ∧ V=twoProduct D.ports e f Q B := by
    have hV : V=twoProduct D.ports e f Q B := by
      funext x
      have h1 := congrFun (identities 1 (Roots.one m)) x
      have h2 := congrFun (identities t ht) x
      simp only [tensorPencil,twoProduct,matrixPencil] at h1 h2 ⊢
      have hh : (t-1)*(V x-Q (x (D.ports (e,false))) (x (D.ports (e,true)))*B (x (D.ports (f,false))) (x (D.ports (f,true))))=0 := by
        linear_combination h2-h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ht1))
    refine ⟨?_,hV⟩
    funext x
    have h1 := congrFun (identities 1 (Roots.one m)) x
    have hv := congrFun hV x
    simp only [tensorPencil,twoProduct,matrixPencil] at h1 hv ⊢
    linear_combination h1-hv
  exact ⟨⟨D.ports,e,f,hef,Q,D.fixed_mem e,A,B,hAB.1,hAB.2,sample⟩⟩

end Holant.Dihedral.SixPortBase
