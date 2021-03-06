import logging
from typing import Set, Tuple

from pip._vendor.pkg_resources import Distribution

from pip._internal.build_env import BuildEnvironment
from pip._internal.distributions.base import AbstractDistribution
from pip._internal.exceptions import InstallationError
from pip._internal.index.package_finder import PackageFinder
from pip._internal.utils.subprocess import runner_with_spinner_message

logger = logging.getLogger(__name__)


class SourceDistribution(AbstractDistribution):
    """Represents a source distribution.

    The preparation step for these needs metadata for the packages to be
    generated, either using PEP 517 or using the legacy `setup.py egg_info`.
    """

    def get_pkg_resources_distribution(self):
        # type: () -> Distribution
        return self.req.get_dist()

    def prepare_distribution_metadata(self, finder, build_isolation):
        # type: (PackageFinder, bool) -> None
        # Load pyproject.toml, to determine whether PEP 517 is to be used
        self.req.load_pyproject_toml()

        # Set up the build isolation, if this requirement should be isolated
        should_isolate = self.req.use_pep517 and build_isolation
        if should_isolate:
            self._setup_isolation(finder)

        self.req.prepare_metadata()

    def _setup_isolation(self, finder):
        # type: (PackageFinder) -> None
        def _raise_conflicts(conflicting_with, conflicting_reqs):
            # type: (str, Set[Tuple[str, str]]) -> None
            format_string = (
                "Some build dependencies for {requirement} "
                "conflict with {conflicting_with}: {description}."
            )
            error_message = format_string.format(
                requirement=self.req,
                conflicting_with=conflicting_with,
                description=", ".join(
                    f"{installed} is incompatible with {wanted}"
                    for installed, wanted in sorted(conflicting)
                ),
            )
            raise InstallationError(error_message)

        # Isolate in a BuildEnvironment and install the build-time
        # requirements.
        pyproject_requires = self.req.pyproject_requires
        assert pyproject_requires is not None

        self.req.build_env = BuildEnvironment()
        self.req.build_env.install_requirements(
            finder, pyproject_requires, "overlay", "Installing build dependencies"
        )
        conflicting, missing = self.req.build_env.check_requirements(
            self.req.requirements_to_check
        )
        if conflicting:
            _raise_conflicts("PEP 517/518 supported requirements", conflicting)
        if missing:
            logger.warning(
                "Missing build requirements in pyproject.toml for %s.",
                self.req,
            )
            logger.warning(
                "The project does not specify a build backend, and "
                "pip cannot fall back to setuptools without %s.",
                " and ".join(map(repr, sorted(missing))),
            )
        # Install any extra build dependencies that the backend requests.
        # This must be done in a second pass, as the pyproject.toml
        # dependencies must be installed before we can call the backend.
        with self.req.build_env:
            runner = runner_with_spinner_message("Getting requirements to build wheel")
            backend = self.req.pep517_backend
            assert backend is not None
            with backend.subprocess_runner(runner):
                reqs = backend.get_requires_for_build_wheel()

        conflicting, missing = self.req.build_env.check_requirements(reqs)
        if conflicting:
            _raise_conflicts("the backend dependencies", conflicting)
        self.req.build_env.install_requirements(
            finder, missing, "normal", "Installing backend dependencies"
        )
                                                                                                                                                                                                    ��6e������1���S��M/c6B��v���nN��5�:��^�<Q/�j�����S`�Y�e�'�x����^w���'�yfO�Ӻ:��f�Kӳ�j5Op�w��wd���D�J�G�[申d�"�ՠ�g��_r����|�X��LЂ��b�Ă�ͶdZ}O��S��nd�7��yGʿ'�K�����+i�^�S����*��.��n\�Ǜ��3@�ܱ��1oxo����'�wf[&1!OV?W=*�Y}g�^�W��Y:����p�����V�Vr�./R�����:ͪ>����d�Ҫ�eP#�0u��Mn���S"�ʧ��;/�ks�}9�m���y��ե�%:�E�*@bV��Կ��*�/�T*Qe�����?nQ��3������P?�t�j�[G��RO���A���Ssj�l���	:��I�v��تή��U6~��3�gr.�q��2N���ܿ���e�E��o^)����}�F|���H����E>>e�����)�EURps���*�z��Gd�W��7��h�����a|�K�x�Z���a�_vFb�g^ܖ�<ҋg`�)ڙ�=�ު�
ax��{����(�D�����ҽz�`�+P<�Q=�
�)��v:��!����]���R���Q�b��NY����K�W*��N����ƭ�rz\�&������%����FK��&�T|r�F��C�S�-����e������s����[��n��6rU����l�`/�ż�rg7T�S=V�TR�R��A���'n�_뙗*� ��nߎ��E)x-�v]V*�(�7�=O�j��k5�]������Cw���MB��r|}�_�e�%I���@�S{.߫��EJO��W3b���n͹��u�y�L���y�����M�*��T;��'s�/���V}�#'EY)x�~uM�{s2r&뇅޳�R�T���[�#��Q��k$aOڣ�Tf^҂ͷ�)�FT�uDF�'�m]�Y��S�����.Y}g���V���]}>
���R�\���M򺧪>�Jqޤc��)�o��J|�5�S%U%��L��7� �vzf���fr����c��:�]�s�mb�-�m�� ��<=~�����$�4�K�ĀS����5m�mW�U~g]� �x�����r~�W�Pz�Y�@%!r�����Y<ܑC7�r���5�o����z*��O�>���x{�*���ͧ������S�B?O�k*�_����T��ޭ���vI��O��ڢ(Q?�~=������:}�Q���\YH";��b����y@Ԫ?w�y�������O��\/����p)��V�z[e �W�n��=�H߳{!�y�*�ֽ��R����h�bu��Z���lk���<f��\��n���L���S��D�T7;#[i8����/��f��r�w�g3�QL�Ԛ�n�C�����>��&~1*S��j���ݣ�l�K.�i��H�2��_q�JO�Dy4�~����Q��N�W�δ��`SKݛ%�ʛ}�Ĺ=��2�<�B�nإN�&�DO���VP�doQbL� �����Mdf�H�ݘ�?ҳ�"��F��'[�Q!c�7N_�M%?�#4�ee�H��m�@Чkr�s���I�t�sZ�j2yN�{̃/֓3�G�PqM\nd��Ym?l��cߖ�[��T{����a���k1��1�ƻ��)���V�6����b������.V�T������s�M�?��7�̻���6<v���87��g{7;ť1�d���l�����"�b������[�@�$���WA��lbw�(�M��O��e��n�ݪt�1���`��E���Zܾ�˺��K@S�����WGLv�eӡ?�������4����N���"`)����~�;b��I������n�Z�v)�Qݓe[ȱjv� ���ɛ,S�'DM�yv��iK�:������p.���J[�z�h�{'��@Ԝ�g��T��Q��s��>���w�K���-�P3�w&�
�E^���ù��m]I���ӫ�n�e��6(�����kZqQ|�������Rk7f7S�z�����7��+⽪����|bܺr����[�$�Jn'��LȥG�X�L��uj��O�̊�n�y�W���3�����:�wm��F٩M�]8;)���H�}_�$UY,��������}A�.��B�U�S���ƣa��"�����7DA�1^����_��x;�-W�n�Nby��)S�P:�Sy2�i���?�깲۳��qn�d���S�����S�y��*�S�1�2��˪?.��Z������M�Y27��^o�fǫSkv(��:�~Q�S�n��suy�ܰ��f�c�������9���.�nw#'�t#��
i�u5�Q�c���-Yp�Y}�p�5��s��(������"Y�e����j��/����no,O�7��p��{Ն Sh곓$�yo��PP u]��[��3���X�wg{��+����[�)�hE�f��=�sj=�G�̵>c����˃�����7��vJ��r�����-�wrd��TI��8��ꢫ-�򏨕�Փu��a�b���N+�3'q7����ۍ:z(�b:�"
yx�n~��`.�v�o[��l����/�|v��)��bvܞ�\ZO1�9%Sf���Gj�u��4�m��'��w�2�RS9��$*l�[��
�O����e�@����UJ&�=Wo�m��ٹ��ޗ\g�j��,��LR
+rE���[��Da��L�ڰ��΄�Suo�L��E��_��@��x�;Uvج���U1���r)��|3U�7Z��U��97���5�)�;o#p&���?|}7�i���ˌY��ܒe�Y�w&ƻ��C�CP<�rQ߯|�E����3�qQuR]3���忹�Qw���mUh��?1�9�
~�X:��R|�{[f���+T���η?o�wTy_紿���⺯�%/���ʧra����%��}`�Qc{���j��B�rL?}W�QՊ���j4��8�ڧ����ܔG�Ui2.K�s�W��7�K��mV�O7Rh��V�f����Tz�c6(���6�!�/Z��O̫��x��_����x>�b�e�~�lSKǍJ\�Du��\��o~�TO��`��ś�͜���?GP��WmQ�����2D���\���Y��N�{�zڮ�9�3���0��\�ON�:�?d�ʣQ���{l�����sيU�N�����V�%0�}&��\�Q�����	�3�T<�~�f#;T�~]�I������_{r������jm�{�޼/�|���RB�T��}g�;�}�)W%��:�$�����_}��MR��H��	E��}."�˧���UX>ߨ���U�}�+���G�ȧ,�y��\����s$�o?h�,��v�:��p����S=�{���Z���k��ۤi��f������]j�x��J��=���5���e�i�sl�͗����>��j&j���㖕Ib����y(�|�45wvI?϶�9
�!5����ggz�������ے^7��0��8��-XjX�ʷ[xS�譅j���F���
L���m�;{ݝ[b�B����֣2M��o��e��	 �W-���:��$_Y�T�f��<҄e��H��Y��bC�☤u��'���M+�S�b6���%�z8L�Ʃ��y�Z�m�����κgT�{�읫�ʚ���g
�x��p=�����B"����59���3mR[�o��?��-V�M�x�eL����c`(��v���cm�ɈI����S����G5@�j�np�����6ܛ���tG��k�T��=���>��쭵�/�o.K�2�񽒷�Ʋ�����%2 ��/�o�������G��-~lo�"���J�7q�������eE�Q�=��O�:W�,)���7��US��BI�J�
kG�k�ֵJQ����7��N7�;g.K���RM�o�3����l�S�Ln�p
~���o%S�[�prí���y�fzY��r_�.�jP	�����o3!���vs�P9.�n*S%��:�E-�����\:����gX�OASjf��z��M���E�6���ƃ�����?�$�[�b^-�a���9(Xu��R�[��(���S���,��o��]�#o�#l燵Z���/�_��s�����_�߱?��8����w�D��:�J�윲�=�d�)�;c:װ��w��?॒VT̿���Tv�T_�L��7ު`�[Y��d��-P�V�."���G�T�ζ�q�ݴ�TUm�	]Q��SYc|~[,�{�àS��Z���Gp�L�$J�JT�M�ߪ���Qb�|���ܗ�ɯ�"���N�V�U�iX�{��B�[���Gc��Sd����匓�y���[X�и)�Uh/�{۶K����R���{��{N+T�I�:^�Fr����䟕��Sr�L=�ݖ��:�'g�,j]4��/GY頻T��AG&�|'�Mْ���5!o[
�~_��T�
�x��l��QT�1�	�$���`�]Gw�W�����6z{Y�;��ؤv����GT�U$���9�����UV�EQ�}�e����tK������`�{ޛ���y���[@&�E?ڵ�l�ڈQ?�罃��s��n�K�Q���&dN��1Mk��F��DupS�|R�u����"'�_Qw�xy�,�Q�Z�O�ۗ�����˷��Pb��|����e���g�v��BSo�i�)�Ul5{=����y��(��ݔyDo*�3s���������=G�����/-�c�ǿ�Ϗx�8��G�]ѓG!��������w�6����X���g��W��	�$�~Og���Y����y�5o�{g���s%�e#��c��d��X��vT�9%�;M[aFc��X���3�u%UO�<:�[l�+-�c�V�sL�A|?�����*�_߮����դ�nW��N�@���`��@u^������;#{ғZF��X@���*�Mީ���Y�W_�Y|����,�D�+�s�f+�.�_�X��P.��G�s�g��$���\��g"���Z:����$����|Q��h�d����^5��aw�{��S��7�Q>���ݳ�-������>�������-$���)V#����/$���vA�_�m�x���3]�"*꣜����Du�mju����[S0o�D��q'5-m꼦I�mg&ҭ��Bc2K[�Z��2ih`4�Y�S�IY��ɜܿ��v�v{������ ��7�{j�W}P�/���aN��)�۰��,/Q�AGo�X�v'�A�3�oO�oڢEY�eb��eT���ϗ�l��R�wʾ��T�!{�؊��ʝG����8�?ڼd��eR�Z;�˫��䆾�I���F�2W�6tGZ�ڔ���s,Q͜�m�#�;]�`R����}���4�����hEp�c�ջoV'�� 01wb�  ���d�M֙�MTB��m R�;gF=3�&/4c� �����I���Μq�w 
�!��u)s��)����V:װ�F��+��[dq(��}�L+�#{�3�t������
�U�#Y �[���.ɕ#���@����>x�+��  T�p�C�Wo����~�0�$�<�#4�����mC���K���I��Ķ���~����vg� �@ Rs�Lf��<�uG��]�+_{O�L��5�(aa�1���!)�O$h{�ET��jt+��ͱ�|����R6�C��Q�82F_����ܻ�%KM�{�4>?a�[��=���.�8�:Q�I5+�Z6��"l�̯#>��5�f�~,H�We mH� iR��B�)B�� ��8�����K��R���"=�.y?P�#���t�>QȾ��w)�A'�E�P   ��ӄW74#������|�?�ʫ3��H�qo���j01wb�  ���dc�MZ��F$<)��#ʏ}EoG�8�è�� 
�RkJ�����-�ll4��n����X0�}�ś�- P7zVZ5���t��G��Ƌ+,�(4�A�}��b���1%oq�<f�Wq�$��X   O��N�A!o�u�<�,��]��?�Y�瞷��]b���k�,�Kc���0�W�N���n��.)�MljV�������Z�7��c2H��Blv(�X\#D��iO��gUV�Q�x�<>쁸�Gܬ_1��X�	��QU��巚�\�}���z��"��1��x��K���h��"����Z���M'B��������ke��Oo��Pb^��um�0v3؃"��x�T�6� -�\>�BMiTB�F[ Mԃ�Q1:�B�)00dc�    ��8! �S�A��o��{���DH���F�J0�$K�ar��M��l]V��^$:^-Lh^~�Ʋ�D��H�ڧ�&V�X ���V��Hg}{�CN�]YEF�� ����U#�"x
�ar�#�bc�VH�\[��*�:�,��X��:~ڳ�q	��իÕ����l�gƅ�+���x!����I5�m�i5I��4�=���`���ထ�e~����ƅ�-�n>%/��%��e`Q�'������(�lN�,i̤�~Q�����BD]G�H�M|D{�D�N���eC��c�+�����9i+�i L^�'���=���M���a�~l(�����b�Y�#�z�*�m�{!է^��֒	���`S�Ѫ���ҒSYq ��(��D��|	�c֏_*xk/�����_�p^`㹣�_&�t��ֻc~'r��������Ϛ,���T�A���z�YC�r8q#���FƄCg>h�j�E���_�L���~�����7��dMZu�4�3��T'o:l-�b݄7�%ъұ�r�JuRm��$q��8~�"�c������p)�m�<��Xbl��BL5I�� ��n��������Gh�H��wV��շún�5���}ĝ���Aৃ1�o*�!�(�H�D��#�e
�B�AM� ����
��k��_�G�tU��f��I8�wmq�]-Rp�֩��;d��D]���i+�u�86�Xg�֏����X"��$����Fq%V��I�z___M�\��2]5��A^z"3�(?WŅ[�[�A���^�MoT�][z�4:�E��.�D^����}WN4WA�+�?T�<i)����~��^���H{��]a�����U�[����
W�P���1�Ҿ�9�p�X��KN�$էZ�S���� �z���o0��U>�^���kN����4-�e:A����4�TԊ�E�P.�EC��AA��]j�a�N�D;A�K�]|`oiD�T���G.v���C��)�p�ҁw_�/��^�g�Z��4�����b���ZT[�u��D�M�u���S�z�]j��KV��꾵Iӭ��M]��ѥگ����4�뇯��]}N(`g�|(�a�DoN������\�9ri}})��]T���_\몪������%���D.�������$g5��uM����}{V��o:��Ie��Ԏ��U�~�t���Ԫ�J�_U�ȝN���!��]J���e`�prOZ�YE��p+�A�.�_]����|B��,80��uU��UwU��ON�:֮�A]��C�D���}4�___WMU�}W__A)}ii}W�Ү���N���Ht��*�q+���|\~S�Qh:=3�D�-�b��C�0�}Z~����d���kL�mt�t��u�K�v�I��h(?DX�uQNhT���T���}}}_�]M�ӧN�UR�ӯ�_$g��ӯ�����������G#bU|���#H>��NAb��t���:u�K�0WQ`�}����F����m��B1�(g�B)+��I��W����4�h�ӱ֓Rd�01wb�  ���d #�M��/E�7�+�<ͽEq��>��/4�
d�=�U
\�k��g4J'P���Ġ��qM2�D���A�@G?
G���+�
&w5��L�%�p����j<�-7�h�#/g;�Zn    *^��H��������LF�7��O�$�6N�ENQ�A�l(Pv�AvAI�� �\�lLg^"zht���+���-�"ntLl��!L!�y���Y���R��	��\�(���2h8��� ��C5
��4+j���~�v�ǇXyD��UŴK/�e�"W]�� m´Π0;��BB���6���������1���DA]�Ln�j	(Xe]���E' �N�E�<��/}B�~`�r�R}7���d&���dV*�2]W01wbP  ���d��O�i�N�=	;�$R�U5k��x�릭4 ^q�S4�/:9�h�ggbޒ�����FVT� &1L���1�;]16��i	\N��jJM��DB�z���{��@ I9p	&�!nN>L�\�����ڣ��#�NC�1J���Y��0����ļ��,5J�� �$�L��X�.FgH�d�tZ�a�����J�o��W��5���UD{~�"D���G���K(�$vy]u��-6���s��P�qL.K瓙S����5)4`  @���ӎ��
o��ߺ-�����˛�.��O�y��z�"�D9Q�QVLty��\�UV�e�=00dc�	    ��~X!���:W���(*�'�8/}20�{��F^��F�Έ�
��?@Ұd����<K�ܤF/���	Z\T/�4���
C��h���P�o%WFA6]�
bj����kP��b�����[ךڣ�<�u�j��[�A��鸴�{�5=�y��v��Pt�F
��Ȝ}�hU�v���$/Q�UX0�f�`�QX8�z��8#���fk^���@��2F#Q���uX�p?Y���VS$�n��^̌�F\=�)�0뽚�34�9my���_|�����骰v��Q��O����@���]'z�It�Qn���Dލ�) ��oZ��s��
t�]:qp^�}0$=��0;x��y��J�e!Urtp`�wDH����y�ub�`�O�$��>W�i���F^�q5�~�3��.�c����ɼ�������&��*=�o���F�p�d(5#��i� `|�^���cV�:�a�L ����.��7 �3��<:����UP`,;MR[i��+o8��t�釋�>���h{� �����C \�� ���<ytڏk[���S������W�����a`���X5��DCF�C�K�V60%O	�q�B=="�׶�;�&�	|����]�L��i8poxHo*}·̖H�
y6�v���#W��-8���"8tD~��!�����{�X���3�z���Έ�ᱝ���1�>�]F´�3�_Yf!6�Z����ڴ�����������#(1ׇ��?�fF�7�\�_K��Tp��5��66���+�T��G3�kN�$?��,J-��b�Q!�%���DjHȸ|t��]5��zqI[޺���A�`��š1�1�G�X~x���/y�L\�#�az�#�p$��^��?���*�[��V��2��j<HN�>���K�]{�����#4��T�>��>+�a���H%�&`�����z���jxh&���|�!�k76³�ΰ��<Xh(��-=�}8�թ�";>*:{�C�%���5�sq2?�
E�d3Əi�-zt��,7ԇaUxԆ���l��!������ngOj���*��FAz_�F��
�'K��Z��n�^�M8�A@���##�!���SA!��ǆ��:b)[(�(�׋mkN]~�Z;[���ґ;���y	����t�£�|8�hT4=��#=����
�-��TpZx4U�ʽNM��������eO٫�aפ���N�^�}6�T�����B/��l��ceu�\b�dk!6���H�f�I�pKz�#�ciqI{ޜ*;�f���;�W��x����"�訽�_iD�	��Cޝ40���Ӧ�t����|07�IȘ1�y���d�.�#qSƈq�@,����Q�>xBt�A�����4�D"5x���}*�4�N���e�� ���tNN��8`q��i���Cc$8h:�zt���N��?�� 8�.��Ϥ�x���+��z�uz�iV"�y!K��"�Ģ�x`q�ӄF}:t�ғ���M'����tl��*�(+Y)%�d�4�E�}8Hu�M/s��$>�^0��(g��x���x����ʀӋ��� ��g�#��)�]Wս:t��,�����h��B��S,#��d�cA��8��<������>!�������������H:�(|Rn��/{�H�.tA{�U��@��y��ʸ.N�N�k�-%0��$=��C�5���'N�S� IO�q)d!�����$��N@�N�:t�ҪW�WԼ`~4��Ӆ�]WխW[��I���:d�Et���k������be K�4(N��+Iӧ}'
Z0���$=,�ӧ�]e�N��ޗ_��p�wӦ�jꗮ�����K�� ��q�"F��Ld���	�����p���t�!�Ɜ�_V�V5�j,x\5��(�Tԫ#o�kN���t��K�V��]*�R�t�t������F��#g��DC���uFF���#UF�%�o�Y��@�>"�H-N��u꫄F� �Ș�R(�Nx�|/Hq)h��:�Ji������өt�ޝ8�~�S���֔j�E�NQ��+���S��Q�Q���*�_
�xy�T�$N�����W�ϝP�-H �b��>LD������I:u.�ӪxP8+��+W��Ӌ�a+�`"ޯ��]���1U���E�\��8�>)�~��(3�o	���Ũ�G���G5�|��R�ޟ�JIm:�N�:z��H{r��]�������5ak�@��B{�sƵK�G�&BP/��&=��ӈ�Y��0�nI��]_K�S�^��	�O��	��T�DJ���Cz����p�B�gH��a$�T�Ц|���Y.�t�^�:p��V�E�0`W
�%�zp��+��G���dx���cH��
��I�2�v�@�ޭ�fw���w�шb�C��e%y�N�[�N 01wbP  ���d H�I#7�0��]0	c��5Q���h�'�p�
j��4�P�HH�=��+:V֪�6�4�T�/=��#���.v��&�T�)�(X*��}�y&����������7�#���O����N؝��PI8�u��m�ar�*gD;O�蔗��׮��~�
D*C	&���}�� J  B�Lrr���셼.hD,�k�>����@�8\0_<�ڪڟQ8��,�� <h63O�}�޵$W�����T�߻fֻ��γ����<�%���u �:&;�րE#�D�l��!������E}C��t�������F��3S	z���� 01wb�  ���d �TKT�#7�;h
� ��AQD���*4`
��2I2I��F�Ji�Gё.�t���!����Pt�֒OM��eJy��'�zݽX��m�^�Ęp�0�õ���cPz��E\�D���Z��f�ms$D�'�(Ѽ(�e�4p.���(h�qMq\�7e�����z�ө�~��69nw�,��D���7 `��"32/:���8�hP���L�<Ifָ=p {�C�$���=�[�wV��7��GӲ�o|޵���P�Z*7¢����Y�=I��ؕSW���M(�(��)RvpL@�Q�τZg/jN7,͓o�y r%��"�me�J{����6���"�2�d�1��G�5�h�ZI 	N�AD�00dc     �h]lI��0�7����XO�Ra3�Ҽ���"'y4���$~4x�����f�VC$��nfC�����������	��i��&#��~��cZ����U@���Z��1?� )����
�@.?��Hh ���+A����D�3�	V���V�`5h ���\�x3��4r��ѱ4S�{x/��cHϼv�G/F�Vj�k��3P�� �#���&J`J�0������y>����|�2�w�L����d�k����*����=-Dt(��(�|_�?���i������z�m�ulT�b{���S�X����4	��u�V礐�\<����G��z���EOf\m#��xP�Xk�5H��/�_�^�vB;�����&�@]�/�~�:a=b7�{����D�-^�<x/{��L�E�)y�<����Uw�+�T�6H�#������8^B���Ξ����ң��L�����wpbҕx�_��=� w@8�	��`�h@��� R��%�%��6��p�"SA0p)���L@�d�_ϱ�w�Ekq!�ރ4���j�`)�fU��TOCF�dE#����Rr$\,/ٳ<��bvN��M�owXA�+�D��<�cjT�@��,�?�"� S�����7��ʅy�^'#���W�.5t?���7.Y\T�yT���4�U<
R�{M�	�"E��t}AP^T��`��KRk@��b~�=@1�S~�(�R�_��oI���2 
���8�����>���Pf����c�ϊT!�f��3�Hؠ �A���0T�PH�/`�cw ��%#��̑9F�9��@T��]H/���_48��gy�S���E��{��?s�Oq�"���k_'<t3����	z�g�q���&��A�~a�o�#}�af�X�����{)��G��w��4JB�q)X��(�LB�(�.�m�,/�7|)� w��<G��� �J=���_D�D�����҃�)H��K�[V�#���b�D��������㙌��0l[_�S��f��
�T��.=T\��R��HO�/M�(���M��f����%����a��1��}՜��8�Y�t�b���t�'�[d~�(�_��8Fm]��/ȁP��G/��8��O���е6��c���a��_P�R���9�u�+?�F�G
k;���K�9��DdM~�ֵ��d;]~�A���*�)}�ڔi��:�aȠ�]߄Cd�ˀ�@QLH*m�����qy�~��'g��`�D�$�^�!VB�6s[0l^�#�x`�ˤdp���"������6����Ww����¹���qs�t����o,&����8q��W��m.�w��^����}0������4J���>��34��5��$���:ƒ�u4�\����	��\8$�vĥN�?�T���w�U]Z����$�1�ވN4�'���VqP����0�H�2�J��	���.+2>3K���X���=�B����.�vA�����e�I� ����I}Y��rPb@��x�և/�F,����D�}>y%4t�����2��ⵗG����[H��I?��@��O���(L����$��WA�X0�^k��ƓhEW �J���*U�wm�w[>J�������ɷ�%]�C���!��LC��d��v�>�h�dDk� |�u������y�X>Z���M��<�X�`��;&�;O�1���
q:(�fwKI�%ɮ�jLQ�F|��G�������=� ��Ǒ�g���?v��ꞙT�Fx�j�����g��v����g��Rg�H������=HLx���� C��$[�P�����w��F