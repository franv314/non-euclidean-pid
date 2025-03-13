import NonEuclideanPid.RingConstruction
import NonEuclideanPid.PrincipalIdeal
import NonEuclideanPid.NotEuclidean

instance R_pid : IsPrincipalIdealRing R :=
  dedekind_hasse_domain_implies_pid R

theorem R_no_ed (ed : Euclidean R) : False := by
  have := euclidean_domain_has_usd R ed not_all_small
  have := no_usd_in_R
  contradiction
