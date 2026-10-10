import Holant.Certificates.EqualityQuaternary.ExoticKleinSource

/-! Numbered-source interfaces A.7/A.8. The four actual retained-state rows
share one exact native-network conclusion. The strengthened row clauses are
also retained, including the C2 sign split and monomial support description.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Holant.EightVertex.ProductAnchor (EndpointEven)
set_option backward.isDefEq.respectTransparency false

inductive SourceRow | c2 | monomial (rotationOrder : ℕ) | standardKlein | exoticKlein

def SourceRow.Valid : SourceRow → Prop
  | .monomial m => 3≤m
  | _ => True

def SourceRepresentatives (F : SignatureFamily Scalar) : SourceRow → Type
  | .c2 => C2.Representatives F
  | .monomial m => MonomialRepresentatives F m
  | .standardKlein => Klein.Representatives F .standard
  | .exoticKlein => Klein.Representatives F .exotic

def SourceGroup : SourceRow → Set Mat
  | .c2 => C2.group
  | .monomial m => groupM m
  | .standardKlein => Klein.group .standard
  | .exoticKlein => Klein.group .exotic

/-- The stable-state convention retains the fixed actual representatives
as current alphabet resources (source lines 5038–5049). -/
def SourceRetained {F : SignatureFamily Scalar} (row : SourceRow) : SourceRepresentatives F row → Prop :=
  match row with
  | .c2 => fun reps => ∀ p,(⟨2,kernelSignature (reps.matrix p)⟩ : AnySignature Scalar)∈F
  | .monomial _ => fun reps => ∀ p t,(⟨2,kernelSignature (reps.matrix p t)⟩ : AnySignature Scalar)∈F
  | .standardKlein => fun reps => Klein.Retained reps
  | .exoticKlein => fun reps => Klein.Retained reps

def SourceDeck {F : SignatureFamily Scalar} (row : SourceRow) :
    SourceRepresentatives F row → Signature Scalar 4 → Prop :=
  match row with
  | .c2 => fun reps q => C2.PhysicalDeck reps q
  | .monomial _ => fun reps q => MonomialPhysicalDeck reps q
  | .standardKlein => fun reps q => Klein.PhysicalDeck reps q
  | .exoticKlein => fun reps q => Klein.PhysicalDeck reps q

def ExactExit (F : SignatureFamily Scalar) (q : Signature Scalar 4) (G : Set Mat) (n : ℕ) : Prop :=
  ∃ N : Network Scalar 4,Boundary.CoreLabels q N ∧ Boundary.Native N ∧ Counted.copies N=n ∧
    EndpointEven N.denote ∧ ¬GroupMatching G N.denote ∧ Gadget.Realizes F .disequality N.denote ∧
      Boundary.Uses F N

def PrimeExit (F : SignatureFamily Scalar) (q : Signature Scalar 4) (G : Set Mat) : Prop :=
  ∃ N : Network Scalar 4,Boundary.CoreLabels q N ∧ Boundary.Native N ∧ Counted.copies N=1 ∧
    EndpointEven N.denote ∧ TensorPrime N.denote ∧ ¬GroupMatching G N.denote ∧
      Gadget.Realizes F .disequality N.denote ∧ Boundary.Uses F N

def BoundaryCertificate (F : SignatureFamily Scalar) (q : Signature Scalar 4) (G : Set Mat) : Prop :=
  ∃ n : ℕ,n≤2 ∧ ExactExit F q G n

theorem PrimeExit.exact {F : SignatureFamily Scalar} {q : Signature Scalar 4} {G : Set Mat}
    (h : PrimeExit F q G) : ExactExit F q G 1 := by
  obtain ⟨N,hl,hn,hc,he,_,hm,hr,hu⟩ := h
  exact ⟨N,hl,hn,hc,he,hm,hr,hu⟩

theorem PrimeExit.certificate {F : SignatureFamily Scalar} {q : Signature Scalar 4} {G : Set Mat}
    (h : PrimeExit F q G) : BoundaryCertificate F q G := ⟨1,by decide,h.exact⟩

theorem counted_labels {q : Signature Scalar 4} {N : Network Scalar 4} (h : Counted.Allowed q N) :
    Boundary.CoreLabels q N := by
  intro v
  rcases h.1 v with hh | hh
  · exact Or.inl hh
  · exact Or.inr (congrArg Sigma.fst hh)

theorem counted_uses {q : Signature Scalar 4} {N : Network Scalar 4} (h : Counted.Allowed q N)
    (F : SignatureFamily Scalar) (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F) : Boundary.Uses F N := by
  intro v
  rcases h.1 v with hh | hh
  · rwa [hh]
  · rwa [hh]

theorem flip_prime_exit (F : SignatureFamily Scalar) (q : Signature Scalar 4) (G : Set Mat)
    (hp : TensorPrime q) (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (mask : Word) (he : EndpointEven (Flip.value q mask)) : PrimeExit F q G := by
  have ha := C2.flip_counted_allowed q mask
  have hp' := flip_prime hp mask
  refine ⟨Flip.network q mask,counted_labels ha,ha.2,C2.flip_counted_copies q mask,?_,?_,?_,
    ha.realizes F hq hI,counted_uses ha F hq hI⟩
  · rwa [Flip.denote]
  · rwa [Flip.denote]
  · rw [Flip.denote]
    exact prime_not_matching hp'

/-- The one-copy output is the explicitly displayed XOR dressing. -/
def FlipChoiceExit (F : SignatureFamily Scalar) (q : Signature Scalar 4) (G : Set Mat) : Prop :=
  ∃ mask : Word, EndpointEven (Flip.value q mask) ∧ TensorPrime (Flip.value q mask) ∧
    ¬GroupMatching G (Flip.value q mask) ∧ Gadget.Realizes F .disequality (Flip.value q mask) ∧
      Boundary.Uses F (Flip.network q mask)

theorem FlipChoiceExit.prime {F : SignatureFamily Scalar} {q : Signature Scalar 4} {G : Set Mat}
    (h : FlipChoiceExit F q G) : PrimeExit F q G := by
  obtain ⟨mask,he,hp,hm,hr,hu⟩ := h
  have ha := C2.flip_counted_allowed q mask
  refine ⟨Flip.network q mask,counted_labels ha,ha.2,C2.flip_counted_copies q mask,?_,?_,?_,?_,hu⟩
  · rwa [Flip.denote]
  · rwa [Flip.denote]
  · rwa [Flip.denote]
  · rwa [Flip.denote]

theorem flip_choice_exit (F : SignatureFamily Scalar) (q : Signature Scalar 4) (G : Set Mat)
    (hp : TensorPrime q) (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (mask : Word) (he : EndpointEven (Flip.value q mask)) : FlipChoiceExit F q G := by
  have ha := C2.flip_counted_allowed q mask
  have hp' := flip_prime hp mask
  refine ⟨mask,he,hp',prime_not_matching hp',?_,counted_uses ha F hq hI⟩
  simpa only [Flip.denote] using ha.realizes F hq hI

/-- The physical output comes from one of the three prescribed joins of two
copies of the actually normalized original q. Normalization and the choice
of the join are conclusions, not supplied classification witnesses. -/
def MixedChoiceExit (F : SignatureFamily Scalar) (q : Signature Scalar 4) : Prop :=
  ∃ (b : Bool) (e : Equiv.Perm (Fin 3)) (x y z : Scalar) (p : Fin 3), x≠0 ∧ z≠0 ∧
    Holant.Projective.CyclicQuaternary.Physical.walsh (C2.Mixed.normalized q b e)=
      C2.Mixed.mixedTable x y z ∧
    ∃ N : Network Scalar 4, Boundary.CoreLabels q N ∧ Boundary.Native N ∧ Counted.copies N=2 ∧
      N.denote=C2.Mixed.output (C2.Mixed.normalized q b e) p ∧
      EndpointEven N.denote ∧ ¬GroupMatching C2.group N.denote ∧
      Gadget.Realizes F .disequality N.denote ∧ Boundary.Uses F N

theorem MixedChoiceExit.exact {F : SignatureFamily Scalar} {q : Signature Scalar 4}
    (h : MixedChoiceExit F q) : ExactExit F q C2.group 2 := by
  obtain ⟨b,e,x,y,z,p,hx,hz,hform,N,hl,hn,hc,hvalue,he,hm,hr,hu⟩ := h
  exact ⟨N,hl,hn,hc,he,hm,hr,hu⟩

theorem source_mixed_choice_exit (F : SignatureFamily Scalar) (reps : C2.Representatives F)
    (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : C2.PhysicalDeck reps q) (hm : ¬C2.OneCopyCase q) : MixedChoiceExit F q := by
  obtain ⟨b,e,x,y,z,hx,hz,hform⟩ := C2.Mixed.source_mixed_normalization reps q hd hm
  let M := C2.Mixed.normalizedNetwork (Counted.input q) b e
  have hM : M.denote=C2.Mixed.normalized q b e := by
    dsimp [M]
    rw [C2.Mixed.normalized_denote,Counted.input_denote]
  have hallowed := C2.Mixed.normalized_allowed (Counted.input_allowed q) b e
  obtain ⟨p,he,hn⟩ := C2.Mixed.normalized_mixed_exit (C2.Mixed.normalized q b e) x y z
    (C2.Mixed.normalized_prime hp b e) hx hz hform
  have ha := C2.Mixed.allowed hallowed p
  refine ⟨b,e,x,y,z,p,hx,hz,hform,C2.Mixed.network M p,counted_labels ha,ha.2,?_,?_,?_,?_,
    ha.realizes F hq hI,counted_uses ha F hq hI⟩
  · rw [C2.Mixed.copies,C2.Mixed.normalized_copies,Counted.input_copies]
  · rw [C2.Mixed.denote,hM]
  · rwa [C2.Mixed.denote,hM]
  · rwa [C2.Mixed.denote,hM]

/-- The exotic choice records its verified atlas word and the optional
exceptional two-leg equality dressing, implemented using actual representatives. -/
def ExoticChoiceExit (F : SignatureFamily Scalar) (q : Signature Scalar 4)
    (reps : Klein.Representatives F .exotic) : Prop :=
  ∃ (j : Fin 24) (flip : Bool), let N := Klein.exoticFinalNetwork reps q j flip
    Boundary.CoreLabels q N ∧ Boundary.Native N ∧ Counted.copies N=1 ∧
      EndpointEven N.denote ∧ TensorPrime N.denote ∧ ¬GroupMatching (Klein.group .exotic) N.denote ∧
      Gadget.Realizes F .disequality N.denote ∧ Boundary.Uses F N

theorem ExoticChoiceExit.prime {F : SignatureFamily Scalar} {q : Signature Scalar 4}
    {reps : Klein.Representatives F .exotic} (h : ExoticChoiceExit F q reps) :
    PrimeExit F q (Klein.group .exotic) := by
  obtain ⟨j,flip,h⟩ := h
  exact ⟨Klein.exoticFinalNetwork reps q j flip,h⟩

def SourceDetail (F : SignatureFamily Scalar) (q : Signature Scalar 4) :
    (row : SourceRow) → SourceRepresentatives F row → Prop
  | .c2,_ =>
      (C2.OneCopyCase q → FlipChoiceExit F q C2.group) ∧
      (¬C2.OneCopyCase q → MixedChoiceExit F q)
  | .monomial m,_ =>
      (∃ (p : Bool) (selected : PairIndex → Bool), (∃ i,selected i=true) ∧
        ∀ w,q w≠0 ↔ ∃ i,selected i=true ∧
          (w=representative p i ∨ w=complement (representative p i))) ∧
      FlipChoiceExit F q (groupM m)
  | .standardKlein,_ => FlipChoiceExit F q (Klein.group .standard)
  | .exoticKlein,reps => ExoticChoiceExit F q reps

/-- Source Theorem A.8 (`thm:cert-interface-equality-q4`), including every
strengthened row clause. Actuality is relative to the current retained F;
the deck-stable definition supplies the literal memberships q∈F and I∈F.
All representative scalars and zero-card branches are explicit in SourceDeck. -/
theorem source_equality_accessible_quaternary_interface (F : SignatureFamily Scalar)
    (row : SourceRow) (hrow : row.Valid) (reps : SourceRepresentatives F row)
    (hret : SourceRetained row reps)
    (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : SourceDeck row reps q) :
    BoundaryCertificate F q (SourceGroup row) ∧ SourceDetail F q row reps := by
  cases row with
  | c2 =>
    have hsimple : C2.OneCopyCase q → FlipChoiceExit F q C2.group := by
      intro hc
      obtain ⟨mask,he⟩ := C2.source_C2_one_copy_endpoint reps q hp.1 hd hc
      exact flip_choice_exit F q C2.group hp hq hI mask he
    have hmixed : ¬C2.OneCopyCase q → MixedChoiceExit F q := by
      intro hc
      exact source_mixed_choice_exit F reps q hp hq hI hd hc
    refine ⟨?_,hsimple,hmixed⟩
    by_cases hc : C2.OneCopyCase q
    · exact (hsimple hc).prime.certificate
    · exact ⟨2,by decide,(hmixed hc).exact⟩
  | monomial m =>
    have hs := source_monomial_support hrow reps q hp.1 hd
    obtain ⟨mask,he⟩ := monomial_endpoint_flip hrow reps q hp.1 hd
    have hx := flip_choice_exit F q (groupM m) hp hq hI mask he
    exact ⟨hx.prime.certificate,hs,hx⟩
  | standardKlein =>
    obtain ⟨mask,he⟩ := Klein.source_standard_endpoint reps q hp.1 hd
    have hx := flip_choice_exit F q (Klein.group .standard) hp hq hI mask he
    exact ⟨hx.prime.certificate,hx⟩
  | exoticKlein =>
    have hx : ExoticChoiceExit F q reps := Klein.source_exotic_choice F reps hret q hp hq hI hd
    exact ⟨hx.prime.certificate,hx⟩

/-- Source Proposition A.7 (`prop:cert-equality-q4-boundary`): an actual
native gadget with at most two original-q vertices yields an endpoint-
nondegenerate eight-vertex tensor outside the current group's matchings. -/
theorem source_physical_equality_accessible_quaternary (F : SignatureFamily Scalar)
    (row : SourceRow) (hrow : row.Valid) (reps : SourceRepresentatives F row)
    (hret : SourceRetained row reps)
    (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : SourceDeck row reps q) : BoundaryCertificate F q (SourceGroup row) :=
  (source_equality_accessible_quaternary_interface F row hrow reps hret q hp hq hI hd).1

end Holant.Certificates.EqualityQuaternary
