# -*- coding: utf-8 -*-

# lefschetz-family
# Copyright (C) 2021  Eric Pichon-Pharabod

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

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
            raise Exception("must tell if fibre and section need to be added")
        return self._add