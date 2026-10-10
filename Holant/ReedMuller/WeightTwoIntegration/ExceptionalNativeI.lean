import Holant.ReedMuller.WeightTwoIntegration.ExceptionalMixedLinks

/-! Source specialization requiring original f and literal I only. X links
are native edges, never assumed to be signature-family vertices. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
open CoefficientAtlas ExceptionalTopology
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def literalI : Signature ℂ 2 := fun x => Signature.equality (x 0) (x 1)

theorem unscaled_exceptional_denote (d : ExceptionalData) (q : Signature ℂ 6) (c : ℂ)
    (hq : q = fun x => c * Signature.coordinateAction (fun _ => walshKernel) (paired d.h) x) :
    (network q (fun e => actualKernel (linkSigns d e))).denote =
      fun x => (16 * c^2) * Signature.coordinateAction (fun _ => walshKernel) (pairedOutput d.Q) x := by
  have hs := network_scalars
    (Signature.coordinateAction (fun _ => walshKernel) (paired d.h))
    (fun e => actualKernel (linkSigns d e)) c (fun _ => 1)
  simp only [one_mul,Finset.prod_const_one,mul_one] at hs
  rw [hq,hs]
  have ht := ExceptionalTransport.denote_action
    (network (paired d.h) (fun e => actualKernel (linkSigns d e))) walshKernel
  change (network (Signature.coordinateAction (fun _ => walshKernel) (paired d.h))
    (fun e => actualKernel (linkSigns d e))).denote =
    Signature.coordinateAction (fun _ => walshKernel)
      (network (paired d.h) (fun e => Kernel.pullback (actualKernel (linkSigns d e)) walshKernel)).denote at ht
  simp_rw [pullback_linkSigns] at ht
  have hs₂ := network_scalars (paired d.h) (characters d.eta d.theta) 1 (fun _ => 2)
  simp only [one_mul,one_pow,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hs₂
  rw [hs₂,exceptional_logical_network,coordinateAction_scalar] at ht
  rw [ht]
  funext x
  ring

def nativeINetwork (d : ExceptionalData) (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6) :
    FiniteNetwork ℂ (Bool ⊕ ExceptionalMixedLinks.ILinks (linkSigns d))
      (ExceptionalMixedLinks.Edges (linkSigns d)) 4 :=
  ExceptionalMixedLinks.network (originalBase p f (fun _ => Signature.disequality)) (linkSigns d)

theorem nativeINetwork_denote (d : ExceptionalData) (p : Equiv.Perm (Fin 6))
    (f : Signature ℂ 6) (c : ℂ)
    (hf : Tensor.reindex p f = fun x =>
      c * Signature.coordinateAction (fun _ => walshKernel) (paired d.h) x) :
    (nativeINetwork d p f).denote = fun x =>
      (16 * c^2) * Signature.coordinateAction (fun _ => walshKernel) (pairedOutput d.Q) x := by
  rw [nativeINetwork,ExceptionalMixedLinks.denote_network]
  change (originalBase p f (fun e => actualKernel (linkSigns d e))).denote = _
  rw [originalBase_denote,unscaled_exceptional_denote d _ c hf]

def sixCopyEquiv (J : Type*) :
    {v : Bool ⊕ J // (match v with | .inl _ => 6 | .inr _ => 2) = 6} ≃ Bool where
  toFun v := match v.val with | .inl b => b | .inr _ => false
  invFun b := ⟨.inl b,rfl⟩
  left_inv := by rintro ⟨b|j,h⟩; rfl; norm_num at h
  right_inv := by intro b; rfl

def sixDressedCopyEquiv (J : Type*) :
    {v : (Bool ⊕ J) ⊕ Unit //
      (match v with | .inl (.inl _) => 6 | .inl (.inr _) => 2 | .inr _ => 2) = 6} ≃ Bool where
  toFun v := match v.val with | .inl (.inl b) => b | _ => false
  invFun b := ⟨.inl (.inl b),rfl⟩
  left_inv := by rintro ⟨(b|j)|u,h⟩; rfl; norm_num at h; norm_num at h
  right_inv := by intro b; rfl

theorem nativeINetwork_two_copies (d : ExceptionalData) (p : Equiv.Perm (Fin 6))
    (f : Signature ℂ 6) : TwoSixPortCopies (nativeINetwork d p f) f := by
  constructor
  · let J := ExceptionalMixedLinks.ILinks (linkSigns d)
    let e : {v : Bool ⊕ J // (nativeINetwork d p f).arity v = 6} ≃
        {v : Bool ⊕ J // (match v with | .inl _ => 6 | .inr _ => 2) = 6} :=
      Equiv.subtypeEquivRight (fun v => by cases v <;> rfl)
    exact (Fintype.card_congr (e.trans (sixCopyEquiv J))).trans Fintype.card_bool
  · rintro (b|e) hv
    · rfl
    · change (2 : ℕ) = 6 at hv
      omega

theorem nativeIDressedNetwork_two_copies (d : ExceptionalData) (p : Equiv.Perm (Fin 6))
    (f : Signature ℂ 6) :
    TwoSixPortCopies (ExceptionalDressing.attachI (nativeINetwork d p f) 1) f := by
  constructor
  · let J := ExceptionalMixedLinks.ILinks (linkSigns d)
    let e : {v : (Bool ⊕ J) ⊕ Unit //
        (ExceptionalDressing.attachI (nativeINetwork d p f) 1).arity v = 6} ≃
        {v : (Bool ⊕ J) ⊕ Unit //
          (match v with | .inl (.inl _) => 6 | .inl (.inr _) => 2 | .inr _ => 2) = 6} :=
      Equiv.subtypeEquivRight (fun v => by rcases v with (b|j)|u <;> rfl)
    exact (Fintype.card_congr (e.trans (sixDressedCopyEquiv J))).trans Fintype.card_bool
  · rintro ((b|e)|u) hv
    · rfl
    · change (2 : ℕ) = 6 at hv
      omega
    · change (2 : ℕ) = 6 at hv
      omega

/-- Actual exceptional anchor from source f and literal I. No X-family
membership or canonical-reindex resource is assumed. The bound is unchanged. -/
theorem exceptional_nativeI_two_copy_even4 {family : SignatureFamily ℂ}
    (d : ExceptionalData) (f : Signature ℂ 6)
    (hfmem : (⟨6,f⟩ : AnySignature ℂ) ∈ family)
    (hI : (⟨2,literalI⟩ : AnySignature ℂ) ∈ family)
    (p : Equiv.Perm (Fin 6)) (c : ℂ) (hc : c ≠ 0)
    (hf : Tensor.reindex p f = fun x =>
      c * Signature.coordinateAction (fun _ => walshKernel) (paired d.h) x) :
    ∃ N : Network ℂ 4, ∃ s : ℂ,
      s ≠ 0 ∧ N.denote = (fun x => s * even4 x) ∧
      N.shape.vertices ≤ 7 ∧ N.shape.edges ≤ 9 ∧
      Fintype.card {v : Fin N.shape.vertices // N.shape.arity v = 6} = 2 ∧
      (∀ v, N.shape.arity v = 6 → HEq (N.vertex v) f) ∧
      (∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ family) ∧
      (∀ e, N.edge e = Signature.disequality) := by
  have hs : (16 * c^2) * (2 * d.coefficient) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc))
      (mul_ne_zero (by norm_num) d.coefficient_ne_zero)
  have hu : ∀ v, (⟨(nativeINetwork d p f).arity v,(nativeINetwork d p f).vertex v⟩ :
      AnySignature ℂ) ∈ family := by
    rintro (b|e)
    · exact hfmem
    · exact hI
  have hn := ExceptionalMixedLinks.iLinks_card_le (linkSigns d)
  have hd := nativeINetwork_denote d p f c hf
  rcases d.sigma_sign with hσ | hσ
  · refine ⟨(nativeINetwork d p f).toNetwork,(16 * c^2) * (2 * d.coefficient),
      hs,?_,?_,?_,?_,?_,uses_toNetwork _ _ hu,?_⟩
    · rw [FiniteNetwork.denote_toNetwork,hd,exceptional_reconstruction_even d hσ]
      funext x
      ring
    · change (ExceptionalMixedLinks.network _ _).toNetwork.shape.vertices ≤ 7
      rw [ExceptionalMixedLinks.vertex_count]
      simp only [Fintype.card_bool,Fintype.card_fin] at hn ⊢
      omega
    · change (ExceptionalMixedLinks.network _ _).toNetwork.shape.edges ≤ 9
      rw [ExceptionalMixedLinks.edge_count]
      simp only [Fintype.card_fin] at hn ⊢
      omega
    · exact (two_copies_toNetwork _ f (nativeINetwork_two_copies d p f)).1
    · exact (two_copies_toNetwork _ f (nativeINetwork_two_copies d p f)).2
    · intro e
      rfl
  · let N := ExceptionalDressing.attachI (nativeINetwork d p f) 1
    have hN : ∀ v, (⟨N.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ family := by
      rintro (v|u)
      · exact hu v
      · change (⟨2,fun x => (1 : ℂ) * literalI x⟩ : AnySignature ℂ) ∈ family
        simpa only [one_mul] using hI
    refine ⟨N.toNetwork,(16 * c^2) * (2 * d.coefficient),
      hs,?_,?_,?_,?_,?_,uses_toNetwork _ _ hN,?_⟩
    · rw [FiniteNetwork.denote_toNetwork]
      change (ExceptionalDressing.attachI (nativeINetwork d p f) 1).denote = _
      rw [ExceptionalDressing.denote_attachI,hd,exceptional_reconstruction_odd d hσ]
      funext x
      dsimp only
      rw [flipFirst_twice]
      ring
    · change (ExceptionalDressing.attachI _ _).toNetwork.shape.vertices ≤ 7
      rw [ExceptionalDressing.vertex_count]
      simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at hn ⊢
      omega
    · change (ExceptionalDressing.attachI _ _).toNetwork.shape.edges ≤ 9
      rw [ExceptionalDressing.edge_count]
      have he := ExceptionalMixedLinks.edge_count
        (originalBase p f (fun _ => Signature.disequality)) (linkSigns d)
      change Fintype.card (ExceptionalMixedLinks.Edges (linkSigns d)) =
        Fintype.card (Fin 4) + Fintype.card (ExceptionalMixedLinks.ILinks (linkSigns d)) at he
      rw [he]
      simp only [Fintype.card_fin] at hn ⊢
      omega
    · exact (two_copies_toNetwork _ f (nativeIDressedNetwork_two_copies d p f)).1
    · exact (two_copies_toNetwork _ f (nativeIDressedNetwork_two_copies d p f)).2
    · intro e
      change N.edge _ = _
      generalize (Fintype.equivFin (ExceptionalMixedLinks.Edges (linkSigns d) ⊕ Unit)).symm e = w
      cases w <;> rfl

theorem exceptional_nativeI_realizes_even4 {family : SignatureFamily ℂ}
    (d : ExceptionalData) (f : Signature ℂ 6)
    (hfmem : (⟨6,f⟩ : AnySignature ℂ) ∈ family)
    (hI : (⟨2,literalI⟩ : AnySignature ℂ) ∈ family)
    (p : Equiv.Perm (Fin 6)) (c : ℂ) (hc : c ≠ 0)
    (hf : Tensor.reindex p f = fun x =>
      c * Signature.coordinateAction (fun _ => walshKernel) (paired d.h) x) :
    Gadget.RealizesUpTo family .disequality even4 := by
  obtain ⟨N,s,hs,hden,_,_,_,_,hv,he⟩ :=
    exceptional_nativeI_two_copy_even4 d f hfmem hI p c hc hf
  refine ⟨s,hs,?_⟩
  rw [← hden]
  exact Gadget.realizes_network N family .disequality hv he

end Holant.ReedMuller.WeightTwoIntegration
