import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.Certified
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.Soundness


namespace Holant.LocalDrafts.MainChain.TransformRecognition.PositiveWitnessSearch
open Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
open ComplexIsolation PowerArithmetic
variable {m k : ℕ}

abbrev Candidate (m k : ℕ) := MatrixWitness.RawCandidate m k × Certificate

def check (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k))
    (c : Candidate m k) : Bool :=
  decide (c.1.2.2.1 = RationalBox.ofRectangle c.2.rectangle) &&
    (c.2.check (relationCode c.1.2.1) && MatrixWitness.precheckRaw target S c.1)

def candidates (m k height : ℕ) : List (Candidate m k) :=
  (MatrixWitness.rawThrough m k height).flatMap (fun r =>
    (tuplesThrough (α:=Certificate) 1 height).map (fun t => (r,t 0)))

def first (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k)) :
    List (Candidate m k) → Option (Candidate m k)
  | [] => none
  | c::cs => if check target S c then some c else first target S cs

def searchThrough (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k))
    (height : ℕ) : Option (Candidate m k) :=
  first target S (candidates m k height)

theorem first_checked (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k))
    (cs : List (Candidate m k)) (c : Candidate m k) (h : first target S cs = some c) :
    check target S c = true := by
  induction cs with
  | nil => simp [first] at h
  | cons a cs ih =>
    by_cases ha : check target S a = true
    · simp only [first,ha,ite_true,Option.some.injEq] at h
      subst c
      exact ha
    · have he : check target S a = false := Bool.eq_false_iff.mpr ha
      simp only [first,he,ite_false] at h
      exact ih h

theorem first_exists (target : Fin m → RootCode) (S : EncodedSystem.System m (5+k))
    (cs : List (Candidate m k))
    (h : ∃ c ∈ cs, check target S c = true) :
    ∃ c, first target S cs = some c := by
  induction cs with
  | nil => simp at h
  | cons a cs ih =>
    by_cases ha : check target S a = true
    · exact ⟨a,by simp [first,ha]⟩
    · obtain ⟨c,hc,hcheck⟩ := h
      have hc' : c ∈ cs := by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact False.elim (ha hcheck)
        · exact hc
      obtain ⟨b,hb⟩ := ih ⟨c,hc',hcheck⟩
      exact ⟨b,by simp [first,ha,hb]⟩

/-- The accepted root belongs to the very relation/source box used by the
coordinate arithmetic. Neither an unrelated certificate nor precheck alone
can create a successful return. -/
theorem checked_sound (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i))
    (S : EncodedSystem.System m (5+k)) (c : Candidate m k)
    (hc : check target S c = true) :
    ∃ θ : ℂ, (c.2.rootCode (relationCode c.1.2.1)).Represents θ ∧
      (∀ e ∈ S, MvPolynomial.aeval (fun j => decode θ (c.1.2.2.2.2 j))
        (EncodedSystem.polynomial w e)=0) ∧
      MatrixWitness.checkGuard c.1.2.1 c.1.2.2.2.2 = true := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hbox,hroot,hpre⟩ := hc
  obtain ⟨θ,hθ⟩ := Certificate.check_sound hroot
  have hr : θ^(c.1.1+1)=decode θ c.1.2.1 := by
    apply relation_of_root
    simpa only [RootCode.polynomial,Certificate.rootCode,relationCode_polynomial] using hθ.2.2.1
  have hsource : c.1.2.2.1.Contains θ := by
    rw [hbox]
    exact RationalBox.contains_ofRectangle hθ.2.1
  have hpre' : MatrixWitness.checkCandidate c.1.2.1 c.1.2.2.1 c.1.2.2.2.1
      target S c.1.2.2.2.2 = true := hpre
  simp only [MatrixWitness.checkCandidate, Bool.and_eq_true] at hpre'
  obtain ⟨hs,hg⟩ := hpre'
  exact ⟨θ,hθ,EncodedSystem.check_sound _ _ _ _ S _ θ w hr hsource ht hs,hg⟩

theorem searchThrough_sound (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i))
    (S : EncodedSystem.System m (5+k)) (height : ℕ) (c : Candidate m k)
    (hc : searchThrough target S height = some c) :
    ∃ θ : ℂ, (c.2.rootCode (relationCode c.1.2.1)).Represents θ ∧
      (∀ e ∈ S, MvPolynomial.aeval (fun j => decode θ (c.1.2.2.2.2 j))
        (EncodedSystem.polynomial w e)=0) ∧
      MatrixWitness.checkGuard c.1.2.1 c.1.2.2.2.2 = true :=
  checked_sound target w ht S c (first_checked target S _ c hc)

theorem rawThrough_mono {a b : ℕ} (h : a ≤ b) :
    ∀ r ∈ MatrixWitness.rawThrough m k a, r ∈ MatrixWitness.rawThrough m k b := by
  intro r hr
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
  exact List.mem_map.mpr ⟨t,tuplesThrough_mono h t ht,rfl⟩

/-- Eventual success is proved, not supplied as an algorithm premise. The
input here is an actual solution for a semantic completeness theorem; the
finite-height runtime search does not receive that solution. -/
theorem eventually_some (w : Fin m → AlgebraicComplex) (target : Fin m → RootCode)
    (ht : ∀ i, (target i).Represents (w i : ℂ))
    (S : EncodedSystem.System m (5+k)) (y : Fin (5+k) → AlgebraicComplex)
    (hy : ∀ e ∈ S, MvPolynomial.aeval (fun j => (y j : ℂ))
      (EncodedSystem.polynomial (fun i => (w i : ℂ)) e)=0)
    (hg : y (Fin.castAdd k 4) *
      (y (Fin.castAdd k 0)*y (Fin.castAdd k 3)-
        y (Fin.castAdd k 1)*y (Fin.castAdd k 2))=1) :
    ∃ h, ∀ h' ≥ h, ∃ c, searchThrough target S h' = some c := by
  obtain ⟨θ,r,t,ri,ti,hra,hta,hr,htm,hbox,hmin,hcheck,hrep,hpre,hcoef,hval⟩ :=
    exists_certified_raw w target ht S y hy hg
  refine ⟨max ri ti,?_⟩
  intro h' hh
  apply first_exists
  refine ⟨(r,t),?_,?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨r,rawThrough_mono ((le_max_left ri ti).trans hh) r hr,?_⟩
    apply List.mem_map.mpr
    exact ⟨(fun _ : Fin 1 => t),
      tuplesThrough_mono ((le_max_right ri ti).trans hh) _ htm,rfl⟩
  · simp [check,hbox,hcheck,hpre]

end Holant.LocalDrafts.MainChain.TransformRecognition.PositiveWitnessSearch
