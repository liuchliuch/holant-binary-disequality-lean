import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularCubic

/-! Actual dense-slice entry for the native-M singular receipt. The pins
come from its saved unary factor and retain their common nonzero scalar.
The original dense quaternary remains an actual old-palette resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularSlice
open Holant Holant.Tractable Holant.Algebraic Holant.OpenNetworkComposition
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export GlobalCloseCompletionSingularCubic (parity cubic symmetric corrected_actual)
end C
namespace Pn
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePinAccess
  (scaledPin slice slice_value slice_actual)
end Pn
namespace U
export StableDenseGaugeUnary (palette root root_nonzero unaryReceipt)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

variable {K : Type} [Field K]

theorem even_formula (f : Signature K 3) (full : ∀x,f x≠0 ↔ C.parity x=false) :
    f=C.cubic (f ![false,false,false]) (f ![false,true,true])
      (f ![true,false,true]) (f ![true,true,false]) := by
  have zero (x : Fin 3→Bool) (odd : C.parity x=true) : f x=0 := by
    by_contra hn
    have h := (full x).mp hn
    rw [odd] at h
    contradiction
  have h001 := zero ![false,false,true] rfl
  have h010 := zero ![false,true,false] rfl
  have h100 := zero ![true,false,false] rfl
  have h111 := zero ![true,true,true] rfl
  funext x
  have hx : x=![x 0,x 1,x 2] := by funext i; fin_cases i <;> rfl
  rw [hx]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [C.cubic,C.parity,h001,h010,h100,h111]

theorem full_slice (q : Signature K 4) (p : Bool)
    (full : ∀x,q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p)
    (v : K) (hv : v≠0) :
    ∀x,Pn.slice q (Pn.scaledPin (!p) v) x≠0 ↔ C.parity x=false := by
  intro x
  rw [Pn.slice_value,Bool.not_not,mul_ne_zero_iff]
  simp only [full]
  cases p <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [Holant.Marked.SupportAtlas.parity,C.parity,hv,h0,h1,h2]

/-- The two nonzero symmetric cubic coefficients and every actual physical
correction are constructed internally from the dense row and the scaled pins. -/
theorem exists_symmetric (F : SignatureFamily K) (hI : RetainsIdentity F)
    (q : Signature K 4) (p : Bool)
    (full : ∀x,q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p)
    (actual : Gadget.Realizes F .disequality q)
    (v : K) (hv : v≠0)
    (pins : ∀b,Gadget.Realizes F .disequality (Pn.scaledPin b v)) :
    ∃a b : K,a≠0 ∧ b≠0 ∧ Gadget.Realizes F .disequality (C.symmetric a b) := by
  let f := Pn.slice q (Pn.scaledPin (!p) v)
  have hf := Pn.slice_actual F hI q _ actual (pins (!p))
  have fullF := full_slice q p full v hv
  have ha : f ![false,false,false]≠0 := (fullF _).mpr rfl
  have hb : f ![false,true,true]≠0 := (fullF _).mpr rfl
  have hc : f ![true,false,true]≠0 := (fullF _).mpr rfl
  have hd : f ![true,true,false]≠0 := (fullF _).mpr rfl
  have he := even_formula f fullF
  change Gadget.Realizes F .disequality f at hf
  rw [he] at hf
  refine ⟨v^3*(f ![false,false,false])^4,
    v^3*f ![false,false,false]*f ![false,true,true]*f ![true,false,true]*f ![true,true,false],
    mul_ne_zero (pow_ne_zero _ hv) (pow_ne_zero _ ha),
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hv) ha) hb) hc) hd,?_⟩
  exact C.corrected_actual F hI _ _ _ _ v hf (pins true)

theorem map_symmetric {L : Type} [Field L] (phi : K→+*L) (a b : K) :
    RingHomRealization.mapSignature phi (C.symmetric a b)=C.symmetric (phi a) (phi b) := by
  funext x
  cases hp : C.parity x <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [RingHomRealization.mapSignature,C.symmetric,C.cubic,hp,h0,h1]

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (r : StableDenseGaugeCurrent.SingularReceipt G P)
variable (q : Signature (OI.K G) 4) (p : Bool)
variable (full : ∀x,q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p)
variable (actual : Gadget.Realizes P.family .disequality q)

include full actual in
theorem original_symmetric : ∃a b : OI.K G,a≠0 ∧ b≠0 ∧
    Gadget.Realizes (U.palette G P r).family .disequality (C.symmetric a b) := by
  let pins := (U.unaryReceipt G P r).pinPair G P r
  have hq : Gadget.Realizes (U.palette G P r).family .disequality q := by
    obtain ⟨N,vertices,edges,value⟩ := actual
    exact ⟨N,fun i=>ProgrammeSaturation.retains_old G P (U.root G P r)
      (U.root_nonzero G P r) (by change 0<2; decide) r.actual (vertices i),edges,value⟩
  exact exists_symmetric _ ((U.palette G P r).retainsIdentity G) q p full hq
    pins.scalar pins.nonzero pins.actual

include full actual in
theorem ambient_symmetric : ∃a b : AlgebraicComplex,a≠0 ∧ b≠0 ∧
    Gadget.Realizes (ClosureSourceRows.ambientFamily G (U.palette G P r))
      .disequality (C.symmetric a b) := by
  obtain ⟨a,b,ha,hb,hf⟩ := original_symmetric G P r q p full actual
  refine ⟨ClosureSourceRows.embedding G a,ClosureSourceRows.embedding G b,
    (fun h=>ha ((ClosureSourceRows.embedding G).injective (h.trans (map_zero _).symm))),
    (fun h=>hb ((ClosureSourceRows.embedding G).injective (h.trans (map_zero _).symm))),?_⟩
  have hm := RingHomRealization.realizes_map (ClosureSourceRows.embedding G) hf
  rw [map_symmetric] at hm
  exact hm


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularSlice
end
