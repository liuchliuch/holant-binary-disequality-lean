import Holant.Proofs.Algorithms.TransformRecognition.FiniteBranchEnumeration
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.RootSearchDriver.Enumeration
import Holant.Proofs.Algorithms.TransformRecognition.PositiveWitnessSearch
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Check


namespace Holant.LocalDrafts.MainChain.TransformRecognition.StructuredCatalogue
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open ComplexIsolation
open RootSearchDriver (cross mem_cross)
open FiniteBranchEnumeration (vectors mem_vectors)

def Covers {A : Type*} (F : ℕ → List A) : Prop :=
  ∀ a, ∃ H, ∀ h, H ≤ h → a ∈ F h

def lists {A : Type*} (xs : List A) (h : ℕ) : List (List A) :=
  (List.range (h+1)).flatMap (fun n => (vectors xs n).map List.ofFn)

def sigma {A : ℕ → Type*} (F : (d : ℕ) → ℕ → List (A d)) (h : ℕ) : List (Σ d, A d) :=
  (List.range (h+1)).flatMap (fun d => (F d h).map (fun x => ⟨d,x⟩))

theorem covers_map {A B : Type*} {F : ℕ → List A} (hF : Covers F)
    (f : A → B) (hf : Function.Surjective f) : Covers (fun h => (F h).map f) := by
  intro b
  obtain ⟨a,rfl⟩ := hf b
  obtain ⟨H,hH⟩ := hF a
  exact ⟨H,fun h hh => List.mem_map.mpr ⟨a,hH h hh,rfl⟩⟩

theorem covers_cross {A B : Type*} {F : ℕ → List A} {G : ℕ → List B}
    (hF : Covers F) (hG : Covers G) : Covers (fun h => cross (F h) (G h)) := by
  rintro ⟨a,b⟩
  obtain ⟨H,hH⟩ := hF a
  obtain ⟨K,hK⟩ := hG b
  exact ⟨max H K,fun h hh => mem_cross.mpr
    ⟨hH h ((le_max_left H K).trans hh),hK h ((le_max_right H K).trans hh)⟩⟩

theorem covers_vectors {A : Type*} {F : ℕ → List A} (hF : Covers F) (n : ℕ) :
    Covers (fun h => vectors (F h) n) := by
  classical
  intro v
  choose H hH using fun i => hF (v i)
  refine ⟨Finset.univ.sup H,?_⟩
  intro h hh
  apply mem_vectors
  intro i
  exact hH i h ((Finset.le_sup (Finset.mem_univ i)).trans hh)

theorem covers_lists {A : Type*} {F : ℕ → List A} (hF : Covers F) :
    Covers (fun h => lists (F h) h) := by
  intro xs
  obtain ⟨H,hH⟩ := covers_vectors hF xs.length xs.get
  refine ⟨max H xs.length,?_⟩
  intro h hh
  exact List.mem_flatMap.mpr ⟨xs.length,List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨xs.get,hH h ((le_max_left _ _).trans hh),List.ofFn_get xs⟩⟩

theorem covers_sigma {A : ℕ → Type*} {F : (d : ℕ) → ℕ → List (A d)}
    (hF : ∀ d, Covers (F d)) : Covers (sigma F) := by
  rintro ⟨d,a⟩
  obtain ⟨H,hH⟩ := hF d a
  refine ⟨max H d,?_⟩
  intro h hh
  exact List.mem_flatMap.mpr ⟨d,List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨a,hH h ((le_max_left _ _).trans hh),rfl⟩⟩

def naturals (h : ℕ) : List ℕ := List.range (h+1)
def rationals (h : ℕ) : List ℚ := RootSearchDriver.rationals (RootSearchDriver.Height.cutoff h)
def polynomials (h : ℕ) : List RationalPolynomialCode := lists (cross (naturals h) (rationals h)) h
def balls (h : ℕ) : List RationalBall :=
  (cross (rationals h) (rationals h)).map (fun p => ⟨p.1,p.2⟩)
def boxes (h : ℕ) : List RationalBox :=
  (cross (balls h) (balls h)).map (fun p => ⟨p.1,p.2⟩)

theorem covers_naturals : Covers naturals := by
  intro n
  exact ⟨n,fun h hh => List.mem_range.mpr (by omega)⟩
theorem covers_rationals : Covers rationals := by
  intro q
  exact ⟨(Holant.Algebraic.rationalEncoding.encode q).length,
    fun h hh => RootSearchDriver.rational_mem_of_length q h hh⟩
theorem covers_polynomials : Covers polynomials :=
  covers_lists (covers_cross covers_naturals covers_rationals)
theorem covers_balls : Covers balls :=
  covers_map (covers_cross covers_rationals covers_rationals) _ (fun b => ⟨(b.center,b.radius),rfl⟩)
theorem covers_boxes : Covers boxes :=
  covers_map (covers_cross covers_balls covers_balls) _ (fun b => ⟨(b.re,b.im),rfl⟩)
theorem covers_certificates : Covers RootSearchDriver.certificates := by
  intro c
  exact ⟨(CertificateMachine.certificateEncoding.encode c).length,
    fun h hh => RootSearchDriver.certificate_mem c h hh⟩

def rawAtDegree (m k d h : ℕ) : List
    (PowerArithmetic.Vector d × (RationalBox ×
      ((Fin m → RationalPolynomialCode) × MatrixWitness.Candidate d k))) :=
  cross (vectors (rationals h) (d+1))
    (cross (boxes h) (cross (vectors (polynomials h) m)
      (vectors (vectors (rationals h) (d+1)) (5+k))))
def positive (m k h : ℕ) : List (PositiveWitnessSearch.Candidate m k) :=
  cross (sigma (rawAtDegree m k) h) (RootSearchDriver.certificates h)

theorem covers_positive (m k : ℕ) : Covers (positive m k) :=
  covers_cross (covers_sigma (fun d => covers_cross (covers_vectors covers_rationals (d+1))
    (covers_cross covers_boxes (covers_cross (covers_vectors covers_polynomials m)
      (covers_vectors (covers_vectors covers_rationals (d+1)) (5+k)))))) covers_certificates

def multipliers (n d h : ℕ) : List (NullstellensatzSearch.Poly n d) :=
  lists (cross (vectors (naturals h) n) (vectors (rationals h) (d+1))) h

theorem covers_multipliers (n d : ℕ) : Covers (multipliers n d) :=
  covers_lists (covers_cross (covers_vectors covers_naturals n) (covers_vectors covers_rationals (d+1)))

def negativeAtDegree (m n q d h : ℕ) : List (NullstellensatzSearch.Data m n q d) :=
  (cross (vectors (rationals h) (d+1)) (cross (RootSearchDriver.certificates h)
    (cross (boxes h) (cross (vectors (polynomials h) m) (vectors (multipliers n d h) q))))).map
      (fun p => ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩)
def negative (m n q h : ℕ) : List (NullstellensatzSearch.Candidate m n q) :=
  sigma (negativeAtDegree m n q) h

theorem covers_negative (m n q : ℕ) : Covers (negative m n q) := by
  apply covers_sigma
  intro d
  apply covers_map (covers_cross (covers_vectors covers_rationals (d+1))
    (covers_cross covers_certificates (covers_cross covers_boxes
      (covers_cross (covers_vectors covers_polynomials m) (covers_vectors (covers_multipliers n d) q)))))
  intro r
  exact ⟨(r.relation,r.certificate,r.source,r.expression,r.multiplier),by cases r; rfl⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.StructuredCatalogue
