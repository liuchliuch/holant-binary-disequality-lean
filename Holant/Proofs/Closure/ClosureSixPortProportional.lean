import Holant.Proofs.Closure.ClosureSixPortProportionalSupport
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlas
import Holant.Proofs.Closure.ClosureSixPortUnary

/-! Actual tensor adapters for the finite proportional endpoint obstructions.
Endpoint supports and all scalar-zero flags are derived from the SAME raw
slices. All selected pairs remain the original ordered coordinates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Projective
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace Proportional
open ClosureRootPencil

theorem product_matching_coset {m : ℕ} {q : Signature ℂ 4} (D : Product m q) :
    ∃ k : Fin 3, ∃ a b : Bool, ∀ x : Word 4,
      q x ≠ 0 ↔ MatchingCoset k a b x := by
  let i := D.ports (0,false)
  let j := D.ports (0,true)
  let k := D.ports (1,false)
  let l := D.ports (1,true)
  have distinct : i≠j ∧ i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ k≠l := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    all_goals intro h; have := D.ports.injective h; contradiction
  obtain ⟨key,a,b,shape⟩ := pairing_coset i j k l distinct (D.parity 0) (D.parity 1)
  refine ⟨key,a,b,?_⟩
  intro x
  rw [D.supported]
  have xor_form (a b p : Bool) : b=(a ^^ p) ↔ (a ^^ b)=p := by
    cases a <;> cases b <;> cases p <;> decide
  simpa only [Fin.forall_fin_two,D.parity_spec,xor_form,i,j,k,l] using shape x

theorem line_sector_support {m : ℕ} (hm : 2 ≤ m) (U : Signature ℂ 4) (c : ℂ)
    (nonzero : U ≠ 0)
    (samples : ∀ t : ℂ, t^m=1 → pencil U (c • U) t=0 ∨ RootProduct m (pencil U (c • U) t)) :
    ∃ k : Fin 3, ∃ a b : Bool, ∀ x : Word 4, U x ≠ 0 ↔ MatchingCoset k a b x := by
  obtain ⟨t,ht,coefficient⟩ := nonzero_line_sample hm c
  have sampleNonzero : pencil U (c • U) t ≠ 0 := by
    rw [line_pencil]
    exact smul_ne_zero coefficient nonzero
  obtain ⟨D⟩ := (samples t ht).resolve_left sampleNonzero
  obtain ⟨k,a,b,shape⟩ := product_matching_coset D
  refine ⟨k,a,b,?_⟩
  intro x
  have eq := shape x
  rw [line_pencil] at eq
  simp only [Pi.smul_apply,smul_eq_mul,mul_ne_zero_iff] at eq
  constructor
  · intro hn; exact eq.mp ⟨coefficient,hn⟩
  · intro hm; exact (eq.mpr hm).2

theorem proportional_sector_support {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (dependent : DependentEndpoints (sliceSix h e p false) (sliceSix h e p true))
    (nonzero : ¬ ZeroSector h e p) :
    ∃ k : Fin 3, ∃ a b : Bool, ∃ flags : Bool → Bool,
      (flags false=true ∨ flags true=true) ∧ ∀ z x,
        sliceSix h e p z x ≠ 0 ↔ flags z=true ∧ MatchingCoset k a b x := by
  classical
  rcases dependent with ⟨c,equation⟩ | ⟨c,equation⟩
  · have baseNonzero : sliceSix h e p false ≠ 0 := by
      intro hz
      exact nonzero ⟨hz,by rw [equation,hz,smul_zero]⟩
    have samples : ∀ t : ℂ, t^m=1 →
        pencil (sliceSix h e p false) (c • sliceSix h e p false) t=0 ∨
          RootProduct m (pencil (sliceSix h e p false) (c • sliceSix h e p false) t) := by
      intro t ht
      rw [←equation]
      exact (deck e p t ht).imp_right (rootMatching_iff_product m _).mp
    obtain ⟨k,a,b,shape⟩ := line_sector_support (by omega) _ c baseNonzero samples
    refine ⟨k,a,b,(fun z => if z then decide (c≠0) else true),Or.inl rfl,?_⟩
    intro z x
    cases z
    · simpa using shape x
    · rw [equation]
      simp only [ite_true,decide_eq_true_eq,Pi.smul_apply,smul_eq_mul,
        mul_ne_zero_iff,shape]
  · have baseNonzero : sliceSix h e p true ≠ 0 := by
      intro hz
      exact nonzero ⟨by rw [equation,hz,smul_zero],hz⟩
    have samples : ∀ t : ℂ, t^m=1 →
        pencil (sliceSix h e p true) (c • sliceSix h e p true) t=0 ∨
          RootProduct m (pencil (sliceSix h e p true) (c • sliceSix h e p true) t) := by
      intro t ht
      have tn : t≠0 := by intro hz; simp [hz,show m≠0 by omega] at ht
      have inverseRoot : (t⁻¹)^m=1 := by rw [inv_pow,ht,inv_one]
      have eq : pencil (sliceSix h e p true) (c • sliceSix h e p true) t =
          t • phaseCard h e p t⁻¹ := by
        funext x
        simp only [pencil,phaseCard,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
        rw [congrFun equation x]
        simp only [Pi.smul_apply,smul_eq_mul]
        field_simp
        ring
      rcases deck e p t⁻¹ inverseRoot with zero | actual
      · left; rw [eq,zero,smul_zero]
      · obtain ⟨D⟩ := (rootMatching_iff_product m _).mp actual
        right
        refine ⟨⟨D.ports,D.matrix,t*D.scalar,mul_ne_zero tn D.nonzero,D.rooted,?_⟩⟩
        rw [eq]
        funext x
        change t * phaseCard h e p t⁻¹ x = t * D.scalar * _
        rw [congrFun D.equation x]
        ring
    obtain ⟨k,a,b,shape⟩ := line_sector_support (by omega) _ c baseNonzero samples
    refine ⟨k,a,b,(fun z => if z then true else decide (c≠0)),Or.inr rfl,?_⟩
    intro z x
    cases z
    · rw [equation]
      simp only [Bool.false_eq_true,ite_false,decide_eq_true_eq,Pi.smul_apply,smul_eq_mul,
        mul_ne_zero_iff,shape]
    · simpa using shape x

def reordered (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) : Signature ℂ 6 :=
  fun w => h (fun i => w (e.symm i))

theorem reordered_phase (h : Signature ℂ 6) (e r : Equiv.Perm (Fin 6)) (p : Bool) (t : ℂ) :
    phaseCard (reordered h e) r p t = phaseCard h (r.trans e) p t := rfl

theorem reordered_deck {m : ℕ} (h : Signature ℂ 6) (deck : OrderedRootDeck m h)
    (e : Equiv.Perm (Fin 6)) : OrderedRootDeck m (reordered h e) := by
  intro r p t ht
  rw [reordered_phase]
  exact deck (r.trans e) p t ht

/-- Projection of the SAME raw tensor support is exactly the union of its
two analytic endpoint supports. This does not assert noncancellation. -/
theorem selectedOutputs_eq_endpoints (h : Signature ℂ 6) (S : Finset (Word 6))
    (support : ∀ w, h w ≠ 0 ↔ w ∈ S) (e : Equiv.Perm (Fin 6)) (p : Bool) :
    selectedOutputs S e p=unionSupport (sliceSix h e p false) (sliceSix h e p true) := by
  classical
  ext x
  simp only [ClosureRootPencilCount.mem_unionSupport]
  constructor
  · intro hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hs,hp⟩ := Finset.mem_filter.mp hw
    have hn := (support w).mpr hs
    have reconstruct : fillSix e (w (e 0)) p (residualSix e w)=w := by
      rw [←hp]
      exact fillSix_reconstruct e w
    have endpoint : sliceSix h e p (w (e 0)) (residualSix e w) ≠ 0 := by
      unfold sliceSix; rw [reconstruct]; exact hn
    cases he : w (e 0)
    · left; simpa only [he] using endpoint
    · right; simpa only [he] using endpoint
  · rintro (hx | hx)
    · exact Finset.mem_image.mpr ⟨fillSix e false p x,
        Finset.mem_filter.mpr ⟨(support _).mp hx,fillSix_pair_parity e false p x⟩,
          residualSix_fillSix e false p x⟩
    · exact Finset.mem_image.mpr ⟨fillSix e true p x,
        Finset.mem_filter.mpr ⟨(support _).mp hx,fillSix_pair_parity e true p x⟩,
          residualSix_fillSix e true p x⟩

theorem no_projection_overflow {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (S : Finset (Word 6))
    (support : ∀ w, h w ≠ 0 ↔ w ∈ S) (i j : Fin 6) (p : Bool) :
    ¬ ProjectionOverflow S i j p := by
  intro overflow
  have bound := endpoint_union_le_four hm h deck (pairOrder i j) p
  rw [←selectedOutputs_eq_endpoints h S support] at bound
  exact (not_lt_of_ge bound) overflow.2

theorem no_projection_certificate {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (S : Finset (Word 6))
    (support : ∀ w, h w ≠ 0 ↔ w ∈ S) (i j : Fin 6) (p : Bool) :
    ¬ ProjectionCertificate S i j p := by
  classical
  rintro ⟨distinct,large | three⟩
  · exact no_projection_overflow hm h deck S support i j p ⟨distinct,large⟩
  · let e := pairOrder i j
    have injective : Set.InjOn (residualSix e) {w | w ∈ selectedWords S e p} := by
      apply Finset.card_image_iff.mp
      exact three.2.trans three.1.symm
    have exactSupport := phase_one_support h S support e p injective
    have same : ClosureRootPencil.support (phaseCard h e p 1)=selectedOutputs S e p := by
      ext x
      exact (mem_support _ _).trans (exactSupport x)
    rcases deck e p 1 (by simp) with zero | actual
    · rw [zero] at same
      have card := congrArg Finset.card same
      simp only [ClosureRootPencil.support,Pi.zero_apply,ne_eq,not_true_eq_false,
        Finset.filter_false,Finset.card_empty] at card
      have : (selectedOutputs S e p).card=2 := three.2
      omega
    · have card := ClosureRootPencil.rootMatching_support_card actual
      rw [same] at card
      have : (selectedOutputs S e p).card=2 := three.2
      omega

theorem reordered_endpoint (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (w : Word 6) :
    reordered h e w=sliceSix h e (w 0 ^^ w 1) (w 0) (residualSix (Equiv.refl _) w) := by
  change reordered h e w = sliceSix (reordered h e) (Equiv.refl _) (w 0 ^^ w 1)
    (w 0) (residualSix (Equiv.refl _) w)
  unfold sliceSix
  have reconstruct := fillSix_reconstruct (Equiv.refl (Fin 6)) w
  simp only [Equiv.refl_apply] at reconstruct
  rw [reconstruct]

private theorem sector_parity_relation (p u v : Bool)
    (same : bit p+bit u=bit (!p)+bit v) : u=(!v) := by
  have finite : ∀ p u v : Bool, bit p+bit u=bit (!p)+bit v → u=(!v) := by decide
  exact finite p u v same

private theorem flags_singleton (flags : Bool → Bool)
    (nonempty : flags false=true ∨ flags true=true)
    (notDouble : ¬(flags false=true ∧ flags true=true)) :
    ∃ z : Bool, ∀ a : Bool, flags a=true ↔ a=z := by
  have finite : ∀ flags : Bool → Bool,
      (flags false=true ∨ flags true=true) → ¬(flags false=true ∧ flags true=true) →
        ∃ z : Bool, ∀ a : Bool, flags a=true ↔ a=z := by decide
  exact finite flags nonempty notDouble

private theorem singleton_pair_fixed (ze zo u v : Bool)
    (even : (u ^^ v)=false → u=ze) (odd : (u ^^ v)=true → u=zo) :
    if ze=zo then u=ze else v=ze := by
  have finite : ∀ ze zo u v : Bool,
      ((u ^^ v)=false → u=ze) → ((u ^^ v)=true → u=zo) →
        (if ze=zo then u=ze else v=ze) := by decide
  exact finite ze zo u v even odd

/-- Two nonzero proportional sectors of the actual tensor force an exact
unary factor. Doubled sectors are excluded by a derived forbidden projection;
the two remaining singleton endpoints share an original supported bit. -/
theorem proportional_proportional_unary_split {m : ℕ} (hm : 3 ≤ m)
    (h : Signature ℂ 6) (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6))
    (evenDependent : DependentEndpoints (sliceSix h e false false) (sliceSix h e false true))
    (oddDependent : DependentEndpoints (sliceSix h e true false) (sliceSix h e true true))
    (evenNonzero : ¬ZeroSector h e false) (oddNonzero : ¬ZeroSector h e true) :
    ∃ r : Equiv.Perm (Fin 6), ∃ b : Bool,
      Nonempty (ProperSplit (⟨6,h⟩ : AnySignature ℂ) ⟨1,pointMass b⟩ ⟨5,unaryResidual h r b⟩) := by
  obtain ⟨ke,ae,be,fe,feNonempty,evenShape⟩ :=
    proportional_sector_support hm h deck e false evenDependent evenNonzero
  obtain ⟨ko,ao,bo,fo,foNonempty,oddShape⟩ :=
    proportional_sector_support hm h deck e true oddDependent oddNonzero
  have support : ∀ w, reordered h e w ≠ 0 ↔ w ∈ PPSupport ke ko ae be ao bo fe fo := by
    intro w
    rw [reordered_endpoint]
    cases hp : w 0 ^^ w 1
    · simpa only [PPSupport,Finset.mem_filter,Finset.mem_univ,true_and,hp,Bool.false_eq_true,
        ite_false] using evenShape (w 0) (residualSix (Equiv.refl _) w)
    · simpa only [PPSupport,Finset.mem_filter,Finset.mem_univ,true_and,hp,ite_true]
        using oddShape (w 0) (residualSix (Equiv.refl _) w)
  have relation : (ae ^^ be)=(!(ao ^^ bo)) := by
    obtain ⟨xe,hxe⟩ := matchingCoset_nonempty ke ae be
    obtain ⟨xo,hxo⟩ := matchingCoset_nonempty ko ao bo
    have eWord : ∃ ze, sliceSix h e false ze xe ≠ 0 := by
      rcases feNonempty with hf | hf
      · exact ⟨false,(evenShape false xe).mpr ⟨hf,hxe⟩⟩
      · exact ⟨true,(evenShape true xe).mpr ⟨hf,hxe⟩⟩
    have oWord : ∃ zo, sliceSix h e true zo xo ≠ 0 := by
      rcases foNonempty with hf | hf
      · exact ⟨false,(oddShape false xo).mpr ⟨hf,hxo⟩⟩
      · exact ⟨true,(oddShape true xo).mpr ⟨hf,hxo⟩⟩
    obtain ⟨ze,hze⟩ := eWord
    obtain ⟨zo,hzo⟩ := oWord
    have same := supported_words_same_parity hm h deck (fillSix e ze false xe)
      (fillSix e zo true xo) hze hzo
    rw [parity_fillSix,parity_fillSix,matchingCoset_parity ke ae be xe hxe,
      matchingCoset_parity ko ao bo xo hxo] at same
    exact sector_parity_relation false _ _ same
  have notDouble : ¬((fe false=true ∧ fe true=true) ∨ (fo false=true ∧ fo true=true)) := by
    intro double
    obtain ⟨i,j,p,overflow⟩ := pp_projection_overflow ke ko ae be ao bo fe fo
      feNonempty foNonempty relation double
    exact no_projection_overflow hm (reordered h e) (reordered_deck h deck e) _ support i j p overflow
  obtain ⟨ze,hze⟩ := flags_singleton fe feNonempty (fun h => notDouble (Or.inl h))
  obtain ⟨zo,hzo⟩ := flags_singleton fo foNonempty (fun h => notDouble (Or.inr h))
  have fixed (w : Word 6) (hw : h w ≠ 0) :
      if ze=zo then w (e 0)=ze else w (e 1)=ze := by
    apply singleton_pair_fixed
    · intro hp
      have endpoint : sliceSix h e false (w (e 0)) (residualSix e w) ≠ 0 := by
        unfold sliceSix
        rw [←hp,fillSix_reconstruct]
        exact hw
      exact (hze _).mp ((evenShape _ _).mp endpoint).1
    · intro hp
      have endpoint : sliceSix h e true (w (e 0)) (residualSix e w) ≠ 0 := by
        unfold sliceSix
        rw [←hp,fillSix_reconstruct]
        exact hw
      exact (hzo _).mp ((oddShape _ _).mp endpoint).1
  by_cases same : ze=zo
  · exact ⟨e,ze,⟨splitOneFive h e ze (fun w hw => by simpa [same] using fixed w hw)⟩⟩
  · let r := (Equiv.swap (0 : Fin 6) 1).trans e
    refine ⟨r,ze,⟨splitOneFive h r ze ?_⟩⟩
    intro w hw
    simpa [r,Equiv.trans_apply,Equiv.swap_apply_def,same] using fixed w hw

theorem proportional_proportional_not_prime {m : ℕ} (hm : 3 ≤ m)
    (h : Signature ℂ 6) (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6))
    (evenDependent : DependentEndpoints (sliceSix h e false false) (sliceSix h e false true))
    (oddDependent : DependentEndpoints (sliceSix h e true false) (sliceSix h e true true))
    (evenNonzero : ¬ZeroSector h e false) (oddNonzero : ¬ZeroSector h e true) :
    ¬Prime (⟨6,h⟩ : AnySignature ℂ) := by
  obtain ⟨r,b,split⟩ := proportional_proportional_unary_split hm h deck e
    evenDependent oddDependent evenNonzero oddNonzero
  exact fun hp => hp.2 ⟨⟨1,pointMass b⟩,⟨5,unaryResidual h r b⟩,split⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cSupport_parity : ∀ edge : Fin 6, ∀ a b o z : Bool, ∀ x : Word 4,
    x ∈ CSupport edge a b o z → parity x=bit (a ^^ b) := by decide

theorem cSupport_nonempty (edge : Fin 6) (a b o z : Bool) :
    ∃ x : Word 4, x ∈ CSupport edge a b o z :=
  ⟨cWord edge a b o z false,Finset.mem_image.mpr ⟨false,Finset.mem_univ _,rfl⟩⟩

/-- The C payload is a literal support equation for the original raw slices;
the ruling producer must derive it from the sampled root deck. -/
def ComplementarySector (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (edge : Fin 6) (a b o : Bool) : Prop :=
  ∀ z x, sliceSix h e p z x ≠ 0 ↔ x ∈ CSupport edge a b o z

/-- Genuine P/C and C/P endpoints cannot occur in an all-ordered root deck.
The finite witness is either a forbidden >4 endpoint union, or an actual
nonzero phase-one card with EXACTLY two entries and unique internal lifts. -/
theorem proportional_complementary_impossible {m : ℕ} (hm : 3 ≤ m)
    (h : Signature ℂ 6) (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (dependent : DependentEndpoints (sliceSix h e p false) (sliceSix h e p true))
    (nonzero : ¬ZeroSector h e p) (edge : Fin 6) (a b o : Bool)
    (complementary : ComplementarySector h e (!p) edge a b o) : False := by
  obtain ⟨kp,ap,bp,flags,flagsNonempty,pShape⟩ :=
    proportional_sector_support hm h deck e p dependent nonzero
  have support : ∀ w, reordered h e w ≠ 0 ↔ w ∈ PCSupport kp ap bp flags p edge a b o := by
    intro w
    rw [reordered_endpoint]
    by_cases hp : (w 0 ^^ w 1)=p
    · rw [hp]
      simpa only [PCSupport,Finset.mem_filter,Finset.mem_univ,true_and,ite_eq_left hp]
        using pShape (w 0) (residualSix (Equiv.refl _) w)
    · have hc : (w 0 ^^ w 1)=(!p) := by cases p <;> cases h0 : w 0 <;> cases h1 : w 1 <;> simp_all
      rw [hc]
      simpa only [PCSupport,Finset.mem_filter,Finset.mem_univ,true_and,ite_eq_right hp]
        using complementary (w 0) (residualSix (Equiv.refl _) w)
  have relation : (ap ^^ bp)=(!(a ^^ b)) := by
    obtain ⟨xp,hxp⟩ := matchingCoset_nonempty kp ap bp
    obtain ⟨xc,hxc⟩ := cSupport_nonempty edge a b o false
    have pWord : ∃ z, sliceSix h e p z xp ≠ 0 := by
      rcases flagsNonempty with hf | hf
      · exact ⟨false,(pShape false xp).mpr ⟨hf,hxp⟩⟩
      · exact ⟨true,(pShape true xp).mpr ⟨hf,hxp⟩⟩
    obtain ⟨z,hz⟩ := pWord
    have same := supported_words_same_parity hm h deck (fillSix e z p xp)
      (fillSix e false (!p) xc) hz ((complementary false xc).mpr hxc)
    rw [parity_fillSix,parity_fillSix,matchingCoset_parity kp ap bp xp hxp,
      cSupport_parity edge a b o false xc hxc] at same
    exact sector_parity_relation p _ _ same
  obtain ⟨i,j,gamma,certificate⟩ := pc_projection_certificate kp ap bp flags p edge a b o
    flagsNonempty relation
  exact no_projection_certificate hm (reordered h e) (reordered_deck h deck e) _ support
    i j gamma certificate

end Proportional
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
