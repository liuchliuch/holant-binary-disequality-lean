import Mathlib.RingTheory.SimpleRing.DivisionRing
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Push
import Holant.Proofs.Algorithms.RingHomRealization


namespace Holant.LocalDrafts.MainChain.RingHomDescent
open RingHomRealization
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K L : Type*} [Field K] [Field L]

theorem signature_injective (φ : K →+* L) {n : ℕ} :
    Function.Injective (mapSignature φ (n:=n)) := by
  intro f g h
  funext x
  exact φ.injective (congrFun h x)

theorem vertex_preimage (φ : K →+* L) {F : SignatureFamily K}
    {n : ℕ} (g : Signature L n) (hg : (⟨n,g⟩ : AnySignature L) ∈ mapFamily φ F) :
    ∃ f : Signature K n, (⟨n,f⟩ : AnySignature K) ∈ F ∧ mapSignature φ f=g := by
  obtain ⟨⟨m,f⟩,hf,he⟩ := hg
  change (⟨m,mapSignature φ f⟩ : AnySignature L)=⟨n,g⟩ at he
  cases he
  exact ⟨f,hf,rfl⟩

variable (φ : K →+* L) {F : SignatureFamily K} {n : ℕ}
variable (N : OpenNetwork L n) (hF : ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature L) ∈ mapFamily φ F)

def descendNetwork : OpenNetwork K n where
  shape := N.shape
  vertex v := (vertex_preimage φ (N.vertex v) (hF v)).choose
  edge := N.edge

theorem descend_labels (v : Fin N.shape.vertices) :
    (⟨(descendNetwork φ N hF).shape.arity v,(descendNetwork φ N hF).vertex v⟩ : AnySignature K) ∈ F :=
  (vertex_preimage φ (N.vertex v) (hF v)).choose_spec.1

theorem map_descendNetwork : mapNetwork φ (descendNetwork φ N hF)=N := by
  have hv : (fun v => mapSignature φ ((descendNetwork φ N hF).vertex v))=N.vertex := by
    funext v
    exact (vertex_preimage φ (N.vertex v) (hF v)).choose_spec.2
  cases N with
  | mk shape vertex edge =>
    dsimp only [mapNetwork, descendNetwork] at hv ⊢
    exact congrArg (fun v => (⟨shape, v, edge⟩ : OpenNetwork L n)) hv

theorem descend_tensor : mapSignature φ (descendNetwork φ N hF).tensor=N.tensor := by
  rw [←map_tensor,map_descendNetwork]

theorem realizes_descends {W : EdgeKind} {f : Signature K n}
    (h : Gadget.Realizes (mapFamily φ F) W (mapSignature φ f)) : Gadget.Realizes F W f := by
  obtain ⟨N,hN,hW,ht⟩ := h
  refine ⟨descendNetwork φ N hN,descend_labels φ N hN,hW,?_⟩
  apply signature_injective φ
  rw [descend_tensor,ht]

theorem realizes_iff {W : EdgeKind} {f : Signature K n} :
    Gadget.Realizes (mapFamily φ F) W (mapSignature φ f) ↔ Gadget.Realizes F W f :=
  ⟨realizes_descends φ,realizes_map φ⟩

theorem realizesUpTo_descends {W : EdgeKind} {f : Signature K n}
    (h : Gadget.RealizesUpTo (mapFamily φ F) W (mapSignature φ f)) :
    Gadget.RealizesUpTo F W f := by
  obtain ⟨c,hc,N,hN,hW,ht⟩ := h
  let M := descendNetwork φ N hN
  have hm : mapSignature φ M.tensor=c • mapSignature φ f :=
    (descend_tensor φ N hN).trans ht
  by_cases hf : f=0
  · have hz : M.tensor=0 := by
      apply signature_injective φ
      funext x
      have hp := congrFun hm x
      simpa [hf, mapSignature, Pi.smul_apply, smul_eq_mul] using hp
    refine ⟨1,one_ne_zero,M,descend_labels φ N hN,hW,?_⟩
    funext x
    simpa [hf] using congrFun hz x
  · obtain ⟨x,hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf (funext h)
    let d := M.tensor x / f x
    have hφx : φ (f x) ≠ 0 := fun he => hx (φ.injective (he.trans φ.map_zero.symm))
    have hd : φ d=c := by
      change φ (M.tensor x / f x)=c
      rw [map_div₀]
      have hp : φ (M.tensor x)=c*φ (f x) := congrFun hm x
      rw [hp,mul_div_cancel_right₀ _ hφx]
    have hd0 : d ≠ 0 := by
      intro hz
      exact hc (hd.symm.trans (by rw [hz,map_zero]))
    refine ⟨d,hd0,M,descend_labels φ N hN,hW,?_⟩
    apply signature_injective φ
    rw [hm]
    funext y
    simp only [mapSignature,Pi.smul_apply,smul_eq_mul,map_mul,hd]

theorem realizesUpTo_iff {W : EdgeKind} {f : Signature K n} :
    Gadget.RealizesUpTo (mapFamily φ F) W (mapSignature φ f) ↔ Gadget.RealizesUpTo F W f :=
  ⟨realizesUpTo_descends φ,realizesUpTo_map φ φ.injective⟩

end
end Holant.LocalDrafts.MainChain.RingHomDescent
