all: base interval integers pi1s1 truncation freegroup wedgecircles pullback pushout

base:
	agda Base.agda

interval:
	agda Spaces/IntervalProps.agda

integers:
	agda Integers.agda

pi1s1:
	agda Spaces/LoopSpaceCircle.agda

truncation:
	agda Homotopy/TruncatedHIT.agda
	agda Homotopy/Truncation.agda

freegroup:
	agda Algebra/FreeGroup.agda
	agda Algebra/FreeGroupProps.agda
	agda Algebra/F2NotCommutative.agda

wedgecircles:
	agda Spaces/LoopSpaceWedgeCircles2.agda

pullback:
	agda Homotopy/PullbackDef.agda
	agda Homotopy/PullbackIsPullback.agda
	agda Homotopy/PullbackUP.agda

pushout:
	agda Homotopy/PushoutDef.agda
	agda Homotopy/PushoutIsPushout.agda
	agda Homotopy/PushoutUP.agda


clean:
	rm *.agdai */*.agdai
