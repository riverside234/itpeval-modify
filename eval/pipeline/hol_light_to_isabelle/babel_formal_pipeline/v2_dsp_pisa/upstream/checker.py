"""Copied from local draft_sketch_prove/autoformalization/checker.py (647aa65).
See ORIGIN.md and checker.patch for the small integration changes.
"""
import time


def initialise_env(*args, **kwargs):
    from PisaFlexibleClient import initialise_env as create
    return create(*args, **kwargs)


class Checker(object):
    def __init__(self, working_dir, isa_path, theory_file, port=9000):
        self.working_dir = working_dir
        self.isa_path = isa_path
        self.theory_file = theory_file
        self.port = port

    def _initialize(self):
        print("Initializing environment")
        print("ISA_PATH: %s" % self.isa_path)
        print("THEORY_FILE: %s" % self.theory_file)
        print("WORKING_DIR: %s" % self.working_dir)
        env = initialise_env(
            self.port,
            working_directory=self.working_dir,
            isa_path=self.isa_path,
            theory_file_path=self.theory_file
        )
        if not env.successful_starting:
            detail = getattr(env.stub, "last_error", "")
            raise RuntimeError("PISA failed to initialize; inspect rpc.jsonl and pisa-server.log: " + detail)
        print("Start initialising environment")
        env.post('<initialise>')
        return env

    def _exit(self, env):
        try:
            env.post('exit')
        except:
            print("env.post('exit') timed out")
            pass

    def _parse_output(self, obs):
        """Parse the sledgehammer output, otherwise return an empty string"""
        if '<hammer>' in obs:
            output = obs.split('<hammer>')[0]
        else:
            output = ''
        return output

    def _run_step(self, step, i, tls_name, env):
        obs, reward, done, metadata = env.step_to_top_level_state(
            action=step,
            tls_name=tls_name,
            new_name='default_%d' % i
        )
        error = None
        if 'error:' in obs or 'Step error' in obs or 'Unknown error' in obs:
            error = obs
        return obs, reward, done, metadata, error

    def _run_sledgehammer(self, step, i, tls_name, env):
        # First try heuristics
        for heuristic in ['by auto', 'by simp', 'by blast', 'by fastforce', 'by force', 'by eval', 'by presburger', 'by sos', 'by arith', 'by linarith', 'by (auto simp: field_simps)']:
        # for heuristic in []:
            step_ = step.replace('sledgehammer', heuristic)
            obs, reward, done, metadata, error = self._run_step(step_, i, tls_name, env)
            if error is None:
                obs = '%s <hammer> %s' % (heuristic, obs)
                return obs, reward, done, metadata, error
        # Try sledgehammer
        step = step.replace("sledgehammer", "normalhammer")
        return self._run_step(step, i, tls_name, env)

    def check(self, formal):
        # Initialize environment
        env = self._initialize()

        # Wrap and parse theorem
        theory = formal  # Caller supplies the original dataset header/prefix/target.
        steps = Checker.get_parsed(env, theory)

        done = False
        reward = 0.0
        reason = ''
        success = False
        step_results = []
        tls_name = 'default'
        for i, step in enumerate(steps):
            try:
                time0 = time.time()
                if 'sledgehammer' in step:
                    obs, reward, done, metadata, error = self._run_sledgehammer(step, i, tls_name, env)
                else:
                    obs, reward, done, metadata, error = self._run_step(step, i, tls_name, env)
                step_time = time.time() - time0
                step_results.append(dict(index=i, step=step, output=self._parse_output(obs), step_time=step_time))
                if error is not None:
                    reason = error
                    success = False
                    done = False
                    break
            except Exception as exc:
                # RPC/step failure - end the proof attempt
                success = False
                done = False
                reason = '%s: %s' % (type(exc).__name__, exc)
                step_results.append(dict(index=i, step=step, output=''))
                break

            # Change when successful
            tls_name = 'default_%d' % i

        if done and reward == 1.0:
            success = True

        result = {
            'success': success,
            'reason': reason,
            'num_steps': len(steps),
            'last_step': len(step_results),
            'step_results': step_results,
            'final_state': tls_name,
        }
        # Exit environment
        self._exit(env)
        return result

    @staticmethod
    def minif2f_wrap_theorem(theorem):
        return 'theory Interactive imports HOL.HOL Complex_Main "HOL-Library.Code_Target_Numeral" "HOL-Library.Sum_of_Squares" "Symmetric_Polynomials.Vieta" "HOL-Computational_Algebra.Computational_Algebra" "HOL-Number_Theory.Number_Theory" \n begin\n%s' % theorem

    @staticmethod
    def wrap_theorem(theorem):
        return 'theory Interactive imports Complex_Main \n "HOL-Computational_Algebra.Computational_Algebra" \n "HOL-Number_Theory.Number_Theory" \n begin\n%s' % theorem

    @staticmethod
    def get_parsed(env, theory, tls_name='default'):
        steps = env.post(f"<parse text> ${theory}")
        steps = steps.split('<SEP>')
        steps = [s for s in steps if s.strip() != '']
        # remove weird '$' step and whitespace steps
        steps = [s for s in steps if s != '$' and s.strip() != '']
        return steps

