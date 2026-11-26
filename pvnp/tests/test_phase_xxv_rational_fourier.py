import unittest
from fractions import Fraction as F
from pvnp.phase_xxv.rational_fourier import Arithmetic, field_box, midpoint_step, detector_box
from pvnp.phase_xxv.certified_decision import certified_decision, BudgetExceeded, sqrt_upper


class RationalFourierTests(unittest.TestCase):
    def assert_enclosed(self, interval, expected):
        self.assertLessEqual(interval[0], expected)
        self.assertGreaterEqual(interval[1], expected)

    def test_pi_and_phase(self):
        a = Arithmetic(40)
        re, im = a.exp_i(a.pi())
        self.assert_enclosed(re, F(-1))
        self.assert_enclosed(im, F(0))
        re, im = a.exp_i(a.box(0))
        self.assert_enclosed(re, F(1))
        self.assert_enclosed(im, F(0))

    def test_exact_zero_mode(self):
        # Exact cancellation of the free phases, nonzero real and imaginary parts.
        s = {(0, 0): (F(1, 2), F(1, 4))}
        L, kappa, beta, gamma, t = F(2), F(1), F(3), F(2), F(1, 3)
        z = field_box(s, s, L, kappa, beta, gamma, t, 40)[(0, 0)]
        x, y = s[(0, 0)]
        m = (x*x+y*y)/L**2
        coeff = -beta*m+gamma*m*m
        self.assert_enclosed(z[0], coeff*y)
        self.assert_enclosed(z[1], -coeff*x)

    def test_rounding_certificate(self):
        s = {(0, 0): (F(1, 2), F(1, 4))}
        h = F(1, 16)
        x, y = s[(0, 0)]
        m = x*x+y*y
        c = -m+m*m
        expected = x+h*c*y, y-h*c*x
        result, bound = midpoint_step(s, s, 1, 0, 1, 1, 0, h, 32)
        actual_l1 = sum(abs(a-b) for a,b in zip(result[(0,0)], expected))
        self.assertLessEqual(actual_l1, bound)
        self.assertLess(bound, F(1, 1000000))

    def test_zero_input(self):
        z, error = midpoint_step({}, {(0, 0)}, 1, 0, 1, 1, 0, F(1, 16), 32)
        self.assertEqual(z[(0,0)], (0,0))
        self.assertEqual(error, 0)

    def test_precision_reduces_certificate(self):
        s = {(0, 0): (F(1, 3), F(1, 5))}
        _, lo = midpoint_step(s, s, 2, 1, 1, 1, F(1,4), F(1,16), 24)
        _, hi = midpoint_step(s, s, 2, 1, 1, 1, F(1,4), F(1,16), 48)
        self.assertLess(hi, lo)


    def test_detector_zero_mode(self):
        state={(0,0):(F(1,2),F(1,4))}
        chi={(0,0):(F(3),F(0))}
        lo,hi=detector_box(state,chi,2,1,F(1,3),40)
        self.assert_enclosed((lo,hi), F(3,2)*(F(1,4)+F(1,16)))

    def test_detector_difference_support(self):
        state={(0,0):(F(1,2),F(0)),(1,0):(F(0),F(1,3))}
        chi={(1,0):(F(1),F(0)),(-1,0):(F(1),F(0))}
        # Cross term is purely imaginary at t=0, so its real part vanishes.
        box=detector_box(state,chi,2,0,0,40)
        self.assert_enclosed(box, F(0))
        chi[(2,0)]=(F(100),F(3))
        chi[(-2,0)]=(F(100),F(-3))
        self.assertEqual(detector_box(state,chi,2,0,0,40),box)

    def test_real_detector_required(self):
        with self.assertRaises(ValueError):
            detector_box({(0,0):(1,0)}, {(1,0):(1,0)}, 2,0,0,32)

    def test_sqrt_upper(self):
        for x in [F(0),F(1),F(2),F(7,13)]:
            self.assertGreaterEqual(sqrt_upper(x)**2,x)

    def test_end_to_end_certificate(self):
        initial={(0,0):(F(1,16),F(0))}
        detector={(0,0):(F(1),F(0))}
        params=dict(initial=initial,detector=detector,L=2,kappa=0,
                    beta=F(1,1000),gamma=F(1,1000),T=F(1,32),
                    margin=F(1,10),cutoff=0,max_steps=10)
        a=certified_decision(threshold=F(-1,8),**params)
        b=certified_decision(threshold=F(1,8),**params)
        self.assertIs(a["decision"],True)
        self.assertIs(b["decision"],False)
        self.assert_enclosed(a["interval"],F(1,512))
        self.assertGreaterEqual(a["steps"],1)
        c=certified_decision(threshold=F(1,512),**params)
        self.assertIsNone(c["decision"])

    def test_resource_caps(self):
        with self.assertRaises(BudgetExceeded):
            certified_decision({(0,0):(1,0)},{(0,0):(1,0)},2,0,1,1,1,0,
                               F(1,10),2,max_modes=1)
        with self.assertRaises(ArithmeticError):
            Arithmetic(32,max_taylor_degree=5).exp_i((F(1),F(1)))


    def test_automatic_cutoff_and_promise_totality(self):
        initial={(0,0):(F(1,16),F(0))}
        detector={(0,0):(F(1),F(0))}
        exact=F(1,512)
        margin=F(1,100)
        params=dict(initial=initial,detector=detector,L=2,kappa=0,
                    beta=F(1,1000),gamma=F(1,1000),T=0,margin=margin)
        for direction in [-1,1]:
            a=certified_decision(threshold=exact+direction*margin,**params)
            self.assertIs(a["decision"],direction==-1)
            self.assert_enclosed(a["interval"],exact)
            self.assertLess(a["interval"][1]-a["interval"][0],margin)
            self.assertEqual(a["modes"],(2*a["cutoff"]+1)**2)


    def test_actual_nonlinearity_sideband_first_variation(self):
        # Constant physical amplitude 1, torus length 6, symmetric
        # weighted perturbation in the +/- first Fourier mode.
        # g(1)=-3/2, c=-1, so -i D F(1)[1+i]=-3/2+7i/2.
        eps=F(1,10000)
        S={(0,0),(1,0),(-1,0)}
        def sample(sign):
            return field_box({(0,0):(6,0),
                              (1,0):(sign*eps,sign*eps),
                              (-1,0):(sign*eps,sign*eps)},
                             S,6,0,2,F(1,2),0,48)[(1,0)]
        plus,minus=sample(1),sample(-1)
        a=Arithmetic(48)
        for i,expected in enumerate((F(-3,2),F(7,2))):
            slope=a.div(a.sub(plus[i],minus[i]),a.box(2*eps))
            self.assertLess(max(abs(slope[0]-expected),abs(slope[1]-expected)),
                            F(1,1000000))


if __name__ == "__main__":
    unittest.main()
