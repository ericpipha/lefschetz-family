# -*- coding: utf-8 -*-

import sage.all

from sage.arith.misc import gcd
from sage.rings.integer_ring import ZZ

from .monodromyRepresentation import MonodromyRepresentation

import logging
import time

logger = logging.getLogger(__name__)


class MonodromyRepresentationCurve(MonodromyRepresentation):

    def desingularise_matrix(self, M):
        if M==1:
            return []
        if (M-1).rank() != 1:
            raise Exception("Unknown singular fibre type")
        v = (M-1).image().gen(0)
        n = gcd(v)
        decomposition = [(M-1)/n + 1] * n
        decomposition = [M.change_ring(ZZ) for M in decomposition]
        return decomposition
    
    @property
    def add(self):
        if not hasattr(self, '_add'):
            self._add = 0
        return self._add