import Graffiti84.BasicFacts

/-!
# RootedChung

The rooted Chung lemma (Lemma 2.1 of `docs/full-proof.md`): if deleting the
non-cut vertex `a` lowers the radius by exactly one, the graph contains an
induced path on at least `2r - 1` vertices **containing `a`**.

Batch A: distance infrastructure along geodesics.
-/

namespace Graffiti84

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- On a geodesic walk, every prefix position realizes the distance:
`d(u, getVert i) = i` for `i ≤ length`. -/
theorem dist_getVert_of_length_eq_dist {G : SimpleGraph α}
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    (i : ℕ) (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have hup : (p.take i).length = i := by
    rw [SimpleGraph.Walk.take_length]
    exact Nat.min_eq_left hi
  have hle : G.dist u (p.getVert i) ≤ i := by
    have h := SimpleGraph.dist_le (p.take i)
    rw [hup] at h
    exact h
  rcases Nat.eq_or_lt_of_le hle with h | h
  · exact h
  · exfalso
    have hreach : G.Reachable u (p.getVert i) := (p.take i).reachable
    obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
    have hdroplen : (p.drop i).length = p.length - i :=
      SimpleGraph.Walk.drop_length p i
    have hsplit_len : (q.append (p.drop i)).length
        = q.length + (p.length - i) := by
      rw [SimpleGraph.Walk.length_append]
    have hshort : (q.append (p.drop i)).length < p.length := by
      rw [hsplit_len, hq]
      omega
    have hd := SimpleGraph.dist_le (q.append (p.drop i))
    rw [hp] at hd
    omega

/-- On a geodesic walk, every suffix position realizes the distance:
`d(getVert i, v) = length - i` for `i ≤ length`. -/
theorem dist_getVert_end_of_length_eq_dist {G : SimpleGraph α}
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    (i : ℕ) (hi : i ≤ p.length) :
    G.dist (p.getVert i) v = p.length - i := by
  have hdroplen : (p.drop i).length = p.length - i :=
    SimpleGraph.Walk.drop_length p i
  have hle : G.dist (p.getVert i) v ≤ p.length - i := by
    have h := SimpleGraph.dist_le (p.drop i)
    rw [hdroplen] at h
    exact h
  rcases Nat.eq_or_lt_of_le hle with h | h
  · exact h
  · exfalso
    have hreach : G.Reachable (p.getVert i) v := (p.drop i).reachable
    obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
    have hup : (p.take i).length = i := by
      rw [SimpleGraph.Walk.take_length]
      exact Nat.min_eq_left hi
    have hsplit_len : ((p.take i).append q).length
        = i + q.length := by
      rw [SimpleGraph.Walk.length_append, hup]
    have hshort : ((p.take i).append q).length < p.length := by
      rw [hsplit_len, hq]
      omega
    have hd := SimpleGraph.dist_le ((p.take i).append q)
    rw [hp] at hd
    omega

/-- Vertices at distinct positions of a geodesic are distinct. -/
theorem getVert_ne_of_length_eq_dist {G : SimpleGraph α}
    {u v : α} {p : G.Walk u v} (hp : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i ≠ j) :
    p.getVert i ≠ p.getVert j := by
  intro heq
  have h1 := dist_getVert_of_length_eq_dist hp i hi
  have h2 := dist_getVert_of_length_eq_dist hp j hj
  rw [heq] at h2
  exact hij (h1.symm.trans h2)
