import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Codec


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open ComplexIsolation.RootSearchDriver (cross)
open StructuralListMachine (exactLength)

theorem cross_map {A B C D : Type} (xs : List A) (ys : List B) (f : A → C) (g : B → D) :
    cross (xs.map f) (ys.map g) = (cross xs ys).map (fun p => (f p.1,g p.2)) := by
  simp [cross,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]

theorem vectors_map {A B : Type} (xs : List A) (f : A → B) (n : ℕ) :
    FiniteBranchEnumeration.vectors (xs.map f) n =
      (FiniteBranchEnumeration.vectors xs n).map (fun v i => f (v i)) := by
  induction n with
  | zero =>
    apply congrArg List.singleton
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [FiniteBranchEnumeration.vectors,ih,List.flatMap_map,List.map_flatMap,List.map_map]
    congr 1
    funext a
    congr 1
    funext v
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem exactLength_map {A B : Type} (xs : List A) (f : A → B) (n : ℕ) :
    exactLength (xs.map f) n = (exactLength xs n).map (List.map f) := by
  simp only [exactLength,vectors_map,List.map_map,List.map_ofFn,Function.comp_def]

theorem lists_map {A B : Type} (xs : List A) (f : A → B) (h : ℕ) :
    StructuredCatalogue.lists (xs.map f) h =
      (StructuredCatalogue.lists xs h).map (List.map f) := by
  unfold StructuredCatalogue.lists
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro n hn
  exact exactLength_map xs f n

def relations (d h : ℕ) : List (List ℚ) := exactLength (StructuredCatalogue.rationals h) (d+1)
def expressions (m h : ℕ) : List (List RationalPolynomialCode) :=
  exactLength (StructuredCatalogue.polynomials h) m
def multipliers (n d h : ℕ) : List NegativeCertificateMachine.Poly :=
  StructuredCatalogue.lists
    (cross (exactLength (StructuredCatalogue.naturals h) n) (relations d h)) h
def payloads (m n q d h : ℕ) : List Payload :=
  cross (relations d h) (cross (ComplexIsolation.RootSearchDriver.certificates h)
    (cross (StructuredCatalogue.boxes h)
      (cross (expressions m h) (exactLength (multipliers n d h) q))))

theorem multipliers_eq (n d h : ℕ) :
    multipliers n d h = (StructuredCatalogue.multipliers n d h).map
      NegativeCertificateMachine.polyWire := by
  unfold multipliers relations exactLength
  rw [cross_map,lists_map]
  rfl

theorem multiplier_vectors_eq (n q d h : ℕ) :
    exactLength (multipliers n d h) q =
      (FiniteBranchEnumeration.vectors (StructuredCatalogue.multipliers n d h) q).map
        (fun v => List.ofFn (fun i => NegativeCertificateMachine.polyWire (v i))) := by
  rw [multipliers_eq]
  simp only [exactLength,vectors_map,List.map_map,Function.comp_def]

theorem payloads_eq (m n q d h : ℕ) :
    payloads m n q d h = (StructuredCatalogue.negativeAtDegree m n q d h).map payloadWire := by
  unfold payloads
  rw [multiplier_vectors_eq]
  simp only [relations,expressions,exactLength,StructuredCatalogue.negativeAtDegree,
    payloadWire,cross,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]

def atDegree (r : Request) (d : ℕ) : List NegativeCertificateMachine.Input :=
  (payloads r.coefficients r.variables r.equations.length d r.height).map (load r d)
def catalogue (r : Request) : List NegativeCertificateMachine.Input :=
  (StructuredCatalogue.naturals r.height).flatMap (atDegree r)

theorem atDegree_fromSource {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h d : ℕ) :
    atDegree (fromSource target S h) d =
      (StructuredCatalogue.negativeAtDegree m n S.length d h).map
        (fun c => NegativeCertificateMachine.fromCandidate target S ⟨d,c⟩) := by
  simp only [atDegree,fromSource,NegativeCertificateMachine.systemWire,List.length_map]
  rw [payloads_eq,List.map_map]
  rfl

theorem catalogue_fromSource {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h : ℕ) :
    catalogue (fromSource target S h) =
      (StructuredCatalogue.negative m n S.length h).map
        (NegativeCertificateMachine.fromCandidate target S) := by
  simp only [catalogue,fromSource,StructuredCatalogue.naturals,
    StructuredCatalogue.negative,StructuredCatalogue.sigma,List.map_flatMap,List.map_map]
  apply List.flatMap_congr
  intro d hd
  exact atDegree_fromSource target S h d

theorem generated_shape {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h : ℕ) (c : NegativeCertificateMachine.Input)
    (hc : c ∈ catalogue (fromSource target S h)) : c.shape=true := by
  rw [catalogue_fromSource] at hc
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hc
  exact NegativeCertificateMachine.fromCandidate_shape target S r

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
