import NonEuclideanPid.RingConstruction
import NonEuclideanPid.PrincipalIdeal
import NonEuclideanPid.NotEuclidean

instance R_pid : IsPrincipalIdealRing R :=
  dedekind_hasse_domain_implies_pid R

theorem R_no_ed [ed : EuclideanDomain R] (ext : ed.toCommRing = R_commring) : False := by
  have := euclidean_domain_has_usd ext not_all_small
  have := no_usd_in_R
  contradiction
