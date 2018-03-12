/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.xta.XtaSystem;

public enum Algorithm {

	SEQITP {
		@Override
		public AlgorithmStrategy<?> createStrategy(final XtaSystem system) {
			return ItpStrategy.createForward(system);
		}
	},

	BINITP {
		@Override
		public AlgorithmStrategy<?> createStrategy(final XtaSystem system) {
			return ItpStrategy.createBackward(system);
		}
	},

	LU {
		@Override
		public AlgorithmStrategy<?> createStrategy(final XtaSystem system) {
			return LuStrategy.create(system);
		}
	},

	EXPLSEQITP {
		@Override
		public AlgorithmStrategy<?> createStrategy(final XtaSystem system) {
			return ExplSeqItpStrategy.create(system);
		}
	},

	EXPLBINITP {
		@Override
		public AlgorithmStrategy<?> createStrategy(final XtaSystem system) {
			return ExplBinItpStrategy.create(system);
		}
	},

	EXPLLU {
		@Override
		public AlgorithmStrategy<?> createStrategy(final XtaSystem system) {
			return ExplLuStrategy.create(system);
		}
	};

	public abstract AlgorithmStrategy<?> createStrategy(final XtaSystem system);
}