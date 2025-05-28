import NonEuclideanPid.RingConstruction
import NonEuclideanPid.PrincipalIdeal
import NonEuclideanPid.NotEuclidean

instance R_pid : IsPrincipalIdealRing R :=
  dedekind_hasse_domain_implies_pid R

theorem R_no_ed [ed : EuclideanDomain R] (ext : ed.toCommRing = R_commring) : False := by
  have not_all_small := not_all_small
  rw [←ext] at not_all_small
  have should_have_usd := euclidean_domain_has_usd ed not_all_small
  rw [ext] at should_have_usd
  have := no_usd_in_R
  contradiction
