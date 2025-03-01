import NonEuclideanPid.RingConstruction
import NonEuclideanPid.PrincipalIdeal
import NonEuclideanPid.NotEuclidean

instance R_pid : IsPrincipalIdealRing R :=
  dedekind_hasse_domain_implies_pid R
