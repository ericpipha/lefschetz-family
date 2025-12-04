
# AUTHORS:
#   - Pierre Lairez (2019): initial implementation


import logging

from sage.matrix.constructor import Matrix
from sage.rings.complex_arb import ComplexBallField
from sage.rings.complex_interval_field import ComplexIntervalField_class
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.rings.real_arb import RealBallField
from sage.rings.real_mpfi import RealIntervalField_class, RealIntervalField
from sage.rings.real_mpfr import RR
from sage.rings.real_double import RDF

logger = logging.getLogger(__name__)

class PrecisionError(Exception):
    pass

class IntegerRelations(object):
    def __init__(self, mat, beta=None, threshold=None, min_threshold=10**3,
                 algorithm='fpLLL:proved', fp='xd', **kwd):
        """`mat` is a matrix with real/complex ball/interval coefficients. This class
        computes the lattice of integer relations between the rows of mat.

        """

        logger.info("Computing lattice of integer relations (ambient dimension %d, number of relations %d)."
                    % (mat.nrows(), mat.ncols()))

        m = mat.nrows()
        nrels = mat.ncols()
        if isinstance(mat.base_ring(), ComplexIntervalField_class) or isinstance(mat.base_ring(), ComplexBallField):
            real = mat.apply_map(lambda x: x.real())
            imag = mat.apply_map(lambda x: x.imag())
            self._imat = Matrix.block([[real, imag]])
            nrels *= 2
        else:
            self._imat = mat

        if not isinstance(self._imat.base_ring(), RealIntervalField_class):
            if isinstance(self._imat.base_ring(), RealBallField):
                self._imat = self._imat.change_ring(RealIntervalField(self._imat.base_ring().precision()))
            else:
                raise ValueError

        if not beta is None:
            self._beta = beta
        else:
            self._beta = (1/max(3*x.absolute_diameter() for x in self._imat.list())).floor()

        logger.info("log(beta) = %s" % str(RR(self._beta).log(10)))
        assert self._beta > 100

        if threshold is None:
            threshold = RR(self._beta)**(1/QQ(m))  # This should be quite conservative.
            logger.info("log(threshold) = %s", RR(threshold).log(10))
            if threshold < min_threshold:
                raise PrecisionError
        else:
            logger.info("log(threshold) = %s (forced by caller)", RR(threshold).log(10))


        self._imat = (self._beta*self._imat).apply_map(lambda x : x.center().round())

        self._rawlat = Matrix.block([[self._imat, Matrix.identity(ZZ, m)]])

        logger.info("Running LLL...")
        self._redlat = self._rawlat.LLL(delta=0.75, algorithm=algorithm, fp=fp, **kwd)
        self._norms = [r.norm() for r in self._redlat.change_ring(RR).rows()]

        self.rank = len([n for n in self._norms if n < threshold])
        kappa = RR(2)**(-QQ(m+1)/2)/m

        if self.rank == len(self._norms):
            self._threshold = RR('+Inf')
        else:
            self._threshold = kappa*self._norms[self.rank]
            #assert self.rank == 0 or self._norms[self.rank-1] < self._threshold

        # self._expected_threshold = kappa*RR(self._beta)**(QQ(nrels)/(m - self.rank))

        # This will be ultimately exported to json, so we use primitive types.
        # self._numdata = {
        #     "logB": int(RR(self._threshold.log(10)))
        # }

        # if self.rank > 0:
        #     self._numdata['N'] = int(self._norms[self.rank-1].ceil())
        #     self._numdata['logE'] = int( (self._norms[self.rank-1]/self._beta*m).log(10).ceil() )
        #     self._numdata['rarity'] = int(RR(self._beta).log(10)*(QQ(nrels)/(m - self.rank))) - RDF(1+self._numdata['N']).log(10).ceil()
        # else:
        #     self._numdata['N'] = int(0)
        #     self._numdata['e'] = int(0)
        #     self._numdata['rarity'] = int(0)

        self.basis = self._redlat[:self.rank, nrels:]

    def basis_elements(self):
        self.basis_matrix().rows()

    def threshold(self):
        return self._threshold

    def half_certificate(self):
        return self._numdata

    # TODO Add info on the numeric reliability




