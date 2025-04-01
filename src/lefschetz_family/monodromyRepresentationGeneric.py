# -*- coding: utf-8 -*-

import sage.all

from sage.arith.misc import gcd

from .monodromyRepresentation import MonodromyRepresentation


import logging
import time

logger = logging.getLogger(__name__)


class MonodromyRepresentationGeneric(MonodromyRepresentation):

    def desingularise_matrix(self, M):
        if (M-1).rank() != 1:
            raise Exception("Unknown singular fibre type")
        v = (M-1).image().gen(0)
        n = gcd(v)
        assert n==1, "Unknown singular fibre type"
        decomposition = [M]
        return decomposition

    @property
    def self_intersection_section(self):
        if not hasattr(self, '_self_intersection_section'):
            chi = -1
            self._self_intersection_section = chi
        return self._self_intersection_section

    @property
    def add(self):
        if not hasattr(self, '_add'):
            raise Exception("must tell if fiber and section need to be added")
        return self._add