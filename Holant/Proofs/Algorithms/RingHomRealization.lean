import Holant.Realization


namespace Holant.LocalDrafts.MainChain.RingHomRealization
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K L : Type*} [CommSemiring K] [CommSemiring L]

def mapSignature (φ : K →+* L) {n : ℕ} (f : Signature K n) : Signature L n :=
  fun x => φ (f x)

def mapAny (φ : K →+* L) (f : AnySignature K) : AnySignature L :=
  ⟨f.1,mapSignature φ f.2⟩

def mapFamily (φ : K →+* L) (F : SignatureFamily K) : SignatureFamily L := mapAny φ '' F

def mapNetwork (φ : K →+* L) {n : ℕ} (N : OpenNetwork K n) : OpenNetwork L n where
  shape := N.shape
  vertex := fun v => mapSignature φ (N.vertex v)
  edge := N.edge

theorem map_edge (φ : K →+* L) (E : EdgeKind) (a b : Bool) :
    φ (E.value a b) = E.value a b := by
  cases E <;> cases a <;> cases b <;>
    simp [EdgeKind.value,Signature.equality,Signature.disequality]

theorem map_weight (φ : K →+* L) {n : ℕ} (N : OpenNetwork K n)
    (z : OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool) :
    (mapNetwork φ N).weight z = φ (N.weight z) := by
  simp only [OpenNetwork.weight,mapNetwork,mapSignature,map_mul,map_prod,map_edge]

theorem map_raw (φ : K →+* L) {n : ℕ} (N : OpenNetwork K n) :
    (mapNetwork φ N).raw = mapSignature φ N.raw := by
  classical
  funext x
  simp only [OpenNetwork.raw,mapSignature,map_sum]
  apply Finset.sum_congr rfl
  intro z _
  change (if ∀ j, z (N.shape.boundary j)=x j then (mapNetwork φ N).weight z else 0) = _
  split_ifs <;> simp only [map_weight,map_zero]

theorem map_boundary (φ : K →+* L) {n : ℕ} (N : OpenNetwork K n)
    (i : Fin n) (a b : Bool) :
    (mapNetwork φ N).boundaryKernel i a b = φ (N.boundaryKernel i a b) := by
  unfold OpenNetwork.boundaryKernel
  dsimp only [mapNetwork]
  cases h : N.shape.boundary i with
  | inl p => cases a <;> cases b <;> simp [Signature.equality]
  | inr f => exact (map_edge φ _ a b).symm

theorem map_tensor (φ : K →+* L) {n : ℕ} (N : OpenNetwork K n) :
    (mapNetwork φ N).tensor = mapSignature φ N.tensor := by
  rw [OpenNetwork.tensor,map_raw]
  funext x
  simp [mapSignature,OpenNetwork.tensor,Signature.coordinateAction,map_boundary]

theorem realizes_map (φ : K →+* L) {F : SignatureFamily K} {W : EdgeKind}
    {n : ℕ} {f : Signature K n} (h : Gadget.Realizes F W f) :
    Gadget.Realizes (mapFamily φ F) W (mapSignature φ f) := by
  obtain ⟨N,hF,hW,he⟩ := h
  refine ⟨mapNetwork φ N,?_,hW,?_⟩
  · intro v
    exact ⟨⟨N.shape.arity v,N.vertex v⟩,hF v,rfl⟩
  · rw [map_tensor,he]

theorem realizesUpTo_map (φ : K →+* L) (hφ : Function.Injective φ)
    {F : SignatureFamily K} {W : EdgeKind} {n : ℕ} {f : Signature K n}
    (h : Gadget.RealizesUpTo F W f) :
    Gadget.RealizesUpTo (mapFamily φ F) W (mapSignature φ f) := by
  obtain ⟨c,hc,h⟩ := h
  refine ⟨φ c,fun hz => hc (hφ (hz.trans φ.map_zero.symm)),?_⟩
  have he : mapSignature φ (fun x => c * f x) = fun x => φ c * φ (f x) := by
    funext x
    exact map_mul φ c (f x)
  exact he ▸ realizes_map φ h

end
end Holant.LocalDrafts.MainChain.RingHomRealization
