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

try:
    import sage.all
except ImportError:
    import sage.all__sagemath_modules



from sage.modules.free_module_element import vector
from sage.matrix.constructor import matrix

from .util import Util

class PointedLoop(object):
    def __init__(self, path):
        assert path[0] == path[-1], "given path is not a loop"
        self.path = Util.simplify_path(path)
    
    def __str__(self):
        s = str(self.path)
        if len(s)>=100:
            s = s[:50] + "..." + s[-50:]
        return "loop pointed at " + str(self.path[0]) +" along " + s
    def __repr__(self):
        s = str(self.path)
        if len(s)>=100:
            s = s[:50] + "..." + s[-50:]
        return "loop pointed at " + str(self.path[0]) +" along " + s
    
    def __add__(self, other):
        return PointedLoop(self.path + other.path)
    def __radd__(self, other):
        if other==0:
            return self
        return PointedLoop(self.path + other.path)
        
    def __sub__(self, other):
        return PointedLoop(self.path + list(reversed(other.path)))

    def __neg__(self):
        return PointedLoop(list(reversed(self.path)))
    
    def __rmul__(self, other):
        if other ==0:
            return PointedLoop([self.path[0]])
        if other >0:
            return PointedLoop(self.path * other)
        if other <0:
            return PointedLoop(list(reversed(self.path)) * -other)
        
    def __mul__(self, other):
        if other ==0:
            return PointedLoop([self.path[0]])
        if other >0:
            return PointedLoop(self.path * other)
        if other <0:
            return PointedLoop(list(reversed(self.path)) * -other)
    
    def __iter__(self):
        return iter(self.path)

    def draw(self, basepoint_free=False, **kwds):
        from sage.plot.plot import list_plot
        if not basepoint_free:
            return list_plot([[c.real(), c.imag()] for c in self.path], True, **kwds)
            
        path = self.path[len(self.path)//2:] + self.path[:len(self.path)//2]
        path = Util.simplify_path(path) + [path[0]]
        return list_plot([[c.real(), c.imag()] for c in path], True, **kwds)
    
    def __getitem__(self, i):
        return self.path[i]
    
    def __len__(self):
        return len(self.path)

    @property
    def edges(self):
        edges = []
        for i in range(len(self.path)-1):
            edges += [self.path[i:i+2]]
        return edges
    
def simplify_conjugation(path_indices):
    res = path_indices.copy()
    i=0
    while i<len(res)-1:
        if res[i][0] == res[i+1][0]:
            newp = res[i][1]+res[i+1][1]
            if newp==0:
                res = res[:i]+res[i+2:]
                i=max(i-1,0)
            else:
                res = res[:i]+[(res[i][0], newp)]+res[i+2:]
        else:
            i+=1
    return res

class LoadedPointedLoop(object):
    def __init__(self, fibration, letters):
        self.letters = simplify_conjugation(letters)
        self.fibration = fibration

    def __add__(self, other):
        if other == 0:
            return self
        return LoadedPointedLoop(self.fibration, self.letters + other.letters)
    def __radd__(self, other):
        return self.__add__(other)
        
    def __sub__(self, other):
        return self.__add__(-other)
        
    def __neg__(self):
        newletters = []
        for (i,p) in self.letters:
            newletters = [(i,-p)] + newletters
        return LoadedPointedLoop(self.fibration, newletters)
        
       
    def conjugate(self, other):
        return other + self - other

    def __repr__(self):
        s = str(self.letters)
        if len(s)>200:
            s = s[:50] + "<...>" + s[-50:]
        return "loaded loop with representation " + s
        
    def __str__(self):
        s = str(self.letters)
        if len(s)>200:
            s = s[:50] + "<...>" + s[-50:]
        return "loaded loop with representation " + s
    
    def __len__(self):
        return len(self.letters)
        
    def __getitem__(self, index):
        if isinstance(index, slice):
            # Return a new Foo with the sliced list
            return LoadedPointedLoop(self.fibration, self.letters[index])
        else:
            # Return a single item
            return self.letters[index]

    def __iter__(self):
        return iter(self.letters)

    def __contains__(self, item):
        return item in self.letters

    def index(self, item):
        return self.letters.index(item)
        
    @property
    def monodromy_matrix(self):
        M = 1
        for (i, p) in self.letters:
            M = self.fibration.monodromy_matrices[i]**p * M
        return M

    def extend(self, gamma):
        num_perm = [len(permlist) for permlist in self.fibration.permuting_cycles]
        res = vector([0 for i in range(sum(num_perm))])
        for (i,p) in self.letters:
            e = 1 if p>0 else -1
            for k in range(abs(p)):
                v = (self.fibration.monodromy_matrices[i]**e-1)*gamma
                decomp = matrix([(self.fibration.monodromy_matrices[i]-1)*per for per in self.fibration.permuting_cycles[i]]).solve_left(v)
                start = sum(num_perm[:i])
                for j, c in enumerate(decomp):
                    res[start+j] += c
                gamma = self.fibration.monodromy_matrices[i]**e*gamma
        return res

    @property
    def path(self):
        return sum([p*self.fibration.paths[i] for i,p in self.letters])
        
    @property
    def indices_inside(self):
        totals = [0 for i in range(len(self.fibration.critical_values))]
        for i, p in self.letters:
            totals[i] += p
        assert all([t in [0,1] for t in totals]), "loop is not enclosing a region"
        return [i for i,t in enumerate(totals) if t==1]
    
    def draw(self, **kwds):
        return self.path.draw(**kwds)
    


class HomotopyRepresentation(object):
    def __init__(self, fibration, loaded_paths=None):
        if loaded_paths == None:
            indices = [[(i,1)] for i in range(len(fibration.critical_values))]
            loaded_paths = [LoadedPointedLoop(fibration, i) for i in indices]
        self.loaded_paths = loaded_paths
        self.fibration = fibration

    def __repr__(self):
        s = "homotopy representation with " + str(len(self.loaded_paths)) + " loops"
        for l in self.loaded_paths:
            s += "\n  -  " + l.__str__()
        return s
        
    @property
    def monodromy_representation(self):
        return [l.monodromy_matrix for l in self.loaded_paths]

    def act_by_braid(self, i, p):
        """returns the HomotopyRepresentation obtained by acting with braid i with power p."""
        assert i<len(self.loaded_paths)-1, "braid index is too high"
        indices = self.loaded_paths[:i]
        if p==1:
            indices += [self.loaded_paths[i+1].conjugate(self.loaded_paths[i]), self.loaded_paths[i]]
        elif p==-1:
            indices += [self.loaded_paths[i+1],self.loaded_paths[i].conjugate(-self.loaded_paths[i+1])]
        else:
            raise Exception("braid power i unknown")
        indices += self.loaded_paths[i+2:]
        return HomotopyRepresentation(self.fibration, loaded_paths=indices)

    def act_by_braids(self, list_of_braids):
        res = self
        for i, n in list_of_braids:
            p = -1 if n<0 else 1
            for j in range(abs(n)):
                res = res.act_by_braid(i, p)
        return res

    @property
    def length(self):
        return sum([len(l) for l in self.loaded_paths])
    
def homotopy_representation_from_allowable_loop(allowable_loop):
    fibration = allowable_loop.fibration
    inside_points = allowable_loop.indices_inside
    n = allowable_loop.index((inside_points[0],1))
    AL = allowable_loop
    done = []
    for k in inside_points:
        n = AL.index((k,1))
        c = AL[:n]
        done += [AL[n:n+1].conjugate(c)]
        AL = c + AL[n+1:]
    AL = - allowable_loop + sum(HomotopyRepresentation(allowable_loop.fibration).loaded_paths)
    for k in range(len(fibration.critical_values)):
        if k in inside_points:
            continue
        n = AL.index((k,1))
        c = AL[:n]
        done += [AL[n:n+1].conjugate(c)]
        AL = c + AL[n+1:]
    done[-1] += AL
    return HomotopyRepresentation(fibration, done)