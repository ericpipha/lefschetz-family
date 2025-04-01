# -*- coding: utf-8 -*-


from sage.rings.complex_arb import ComplexBallField
from sage.rings.complex_mpfr import ComplexField

class Context(object):

    def __init__(self,
            method=None,
            singular=False,
            debug=False,
            use_symmetry=True,
            nbits=200,
            long_fibration=True,
            depth=0,
            simultaneous_integration=False
        ):
        r"""
        Lefschetz Family integration context

        Options:

        * ``method`` -- The way the paths are computed, either along a Voronoi diagram of the singularities ("voronoi"), or a Delaunay triangulation of the singularities ("delaunay"). Default is "voronoi"
        * ``compute_periods`` -- Whether the algorithm should compute periods of the variety, or stop at homology. Default is True.
        * ``singular`` -- Whether the input variety is expected to be singular. Default is False

        * (other options still to be documented...)
        """

        if not method in [None, "voronoi", "delaunay_dual"]:
            raise ValueError("method", method)
        self.method = "voronoi" if method==None else method

        if not isinstance(singular, bool):
            raise TypeError("singular", type(singular))
        self.singular = singular
        
        if not isinstance(debug, bool):
            raise TypeError("debug", type(debug))
        self.debug = debug

        if not isinstance(long_fibration, bool):
            raise TypeError("long_fibration", type(debug))
        self.long_fibration = long_fibration

        if not isinstance(simultaneous_integration, bool):
            raise TypeError("simultaneous_integration", type(debug))
        self.simultaneous_integration = simultaneous_integration

        # if not isinstance(nbits, ): # what type is int ?
        #     raise TypeError("nbits", type(nbits))
        self.nbits = nbits

        if not isinstance(use_symmetry, bool):
            raise TypeError("use_symmetry", type(use_symmetry))
        self.use_symmetry = use_symmetry

        # if not isinstance(depth, int):
        #     raise TypeError("depth", type(depth))
        # self.depth = depth

        self.CBF = ComplexBallField(4*nbits)
        self.CF = ComplexField(4*nbits)
        self.depth = depth
        self.cutoff_simultaneous_integration = 2

dctx = Context() # default context
