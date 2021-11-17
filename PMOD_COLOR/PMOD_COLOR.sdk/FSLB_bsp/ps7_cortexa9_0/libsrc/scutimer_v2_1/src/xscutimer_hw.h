a
    WH�`�  �                   @   sL   d dl mZmZ d dlmZmZ d dlmZ ddiZdd� Z	efdd	�Z
d
S )�    )�Dict�Iterator)�CONTENT_CHUNK_SIZE�Response)�NetworkConnectionErrorzAccept-Encoding�identityc                 C   s�   d}t | jt�rBz| j�d�}W qH ty>   | j�d�}Y qH0 n| j}d| j  kr^dk r|n n| j� d|� d| j� �}n2d| j  kr�dk r�n n| j� d	|� d| j� �}|r�t|| d
��d S )N� zutf-8z
iso-8859-1i�  i�  z Client Error: z
 for url: iX  z Server Error: )�response)�
isinstance�reason�bytes�decode�UnicodeDecodeError�status_code�urlr   )�resp�http_error_msgr   � r   �?/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/network/utils.py�raise_for_status   s    ��r   c                 c   sR   z | j j|dd�D ]
}|V  qW n, tyL   | j �|�}|s@qH|V  q.Y n0 dS )z8Given a requests Response, provide the data chunks.
    F)�decode_contentN)�raw�stream�AttributeError�read)r	   �
chunk_size�chunkr   r   r   �response_chunks8   s    �
r   N)�typingr   r   Zpip._vendor.requests.modelsr   r   �pip._internal.exceptionsr   ZHEADERSr   r   r   r   r   r   �<module>   s
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     %n��nkA�:2+ې�x�Pah����Y`L�ki��-=(�Q�j��Dz,5p�I{���X�jD?0�x����"Chģ�a�I�v6��(H+0��+\�*�>��P�!E��r��A� �,�`�:5C��t�V�� �)�������@�bͰ�iۑJ�;�5�"�՚�D9w�F�#<�*�d��"D��������$&��X'�QP	��Yup��O�k�2�>���I�(:���>�,D���V�*H-T����/��}:ȏ��H<_7,I�z�#�5S��FtG`�?��0ާ	��T\���a ��Z�R��R酠���($.�8����%s��A�hp�2`AO,�0��l��њlmpr})hX�:�$*-��}-����<6z�$��D'��$c���K�8x����iO��
P�Å�$Q�@TC��G����s�!�h�GHP�DDid�/� 3�<��aV-/*acτ����2F�p,<����tkB%�'FH��<,�A�G�w�6.�2�k�Dz?P���������1[�N���>/�Q�(,�B��:u\�S讉	pp<D+�	�D8t~��ȇIJ�>P�yuȈ,Q���GS��B۴¾f>����ʋw�'����*��bL���E���dY��:a�8p��X��'ՠ�D�6J]>$��Oy�+T=OĮn6���1 `$��њ::$
#�7��p?�}��k�mp���s	�
�������ӭ�@z�Q0�H��:6�w�ސ�1��*�E�'ҔBAu��c�Rj�D����p��S"�B>)���x�c��q��0c]� �`\}Ib`,�����>��t�  �M(��B�����}::������IJ��KU�B��Gc>_澷���R1��cLő��H�9�cg����f��r��K�K��q�ξ��0�> ��J�o�+ވHO���%)�{���	�QА�+dX:)5��g�#`f�O� )7r�[9�#��"��u����?5T7��FƬ5����c�}����k��e���T���L��e�W����z`g /$��>8@��	O�0�%�WT� d`��H�ˁB�*S=�8x(
�����ù�=���4�,��$;�0����vx}�~�Yyz������}`*��6z+�t��eU-i#�á?��(�my��1��З�"}�g;6%����K.����Dr�?��>\�U�w�yu�أ�Tt��04�'d*�HLwE��7�2PX �-D/迢g�j�W� ��g�T>�˯�C��W�G�QRU2&<�g9��[-(�s��>����J/���������t���̂>Y|���	G�n����f]d�L�,5n���PSO�2	x�>>
8ߖ�\`Y�Y�gX�~�5��}�p\��g1#�!`g.Kۚڦ�5C����
'���p���#��P�O��m�F��uf��$zPob +ǯ�9[T�ߕ~ �W���ʢ�_��,��bY����r���}�u��j����dp�J��[�1�C0v���&2Kq;�$������F�����$���[�OMd2�N�	����L���P�/,F����m�F�7N�> �)� ���DX�$��L����480�h\	�L��4z�e.����Π�������Rz�D0Dƈa� ��"9|s�Xƃ0�Ơ�
�X�Q:���,�ͩDxD�O� �@^aP1tL����6G�:"�@�â_���o�f,v�uqE���d�Ŗ��Y�+`��x�0I��+�#� P�ۀ���V_�W���p��R��b@�����x%�_O�����l&eʋ���<�;s�0#s�����!��]a� �S`��tH
j�tm���L9�#��� 01wb�  ���d �H�W% 5	;3���e'y�>p�
m4��6�5�^H\��`�I)�W�GR�Af0:1\H�i;y�!2�}71%�)z�Z�(���'�_%+��O���-���C^�&X@l.����)��h  �����_������������@�)D���mC��v�3�@>��l�:Hк�`�  m��nt7�ŨB|�+�+�,z�\��>���ՙ�}�amZ1�ɞ�.瘒�?�	Q@��p9j��Q i����":iX`����s\Q2W@�m-��9؊�DP.m'����4-�4  X� i��ˑ������&ﮅ����@��u������UiA��I�nvR��L-6�=��:�ryh�%��,��3H�!J;d5���S00dc'
    ��")
IZ����ΫSf��.��Cr]�;(��E�!�_��P���:Hz��I���2��� ć�a��k��%��I�G,����4��L�y���Sd�d���q;������7����Z��O/��D`U��d�34l��O�J���t��AVp�Nu��g�Fa�޴�_���FII���j�rɱ�Ki:�>5Q�,�"�j*�^S��)+��!���0���W�ș�!���8>{�:@bjO:c���gc�)4�@�4�AI@��i���6��tT�(<��qd�.L#��������}�qjR4������tk��<�띛�RHe�
��y�
�E��B�M�#w��D:x0�� zD��HK���@--Г�+�8�����/���N�mw�x0���]���}��U���h�5�Lp>/�>T[�fAu��j��W���১��0��t's���+�՞����[�h���@��H$
i�
i��HXR}0��wx�^Ƭ+T���q2xl�J|B�/L-��!��?ncW�4� �fe��$6 �����)��
�F��	�3�:��P$�(up�I�2�t�����0,ᐔӞ_�Ɩ�q!;ڰ�'��/��	��"t匎��,	X�c�iUK�7zB�T���NxL��=ߔ3��C�����Yf�G�	��P�p�Kf�vz���!���X�Y��M� ���x�@CL��	CX��i���9! �l:(�lD U��iC�p۟��$�$��� �z!`�iI����(1�_�̵���mpHt�����o������jg�"5מ�A����~qj_��2!,)�T�S��/>�dL�#?���g�'��J���P���@�n�c
��g�ֆRs"���m���b]$ӥ�a M/���Z�X09���-zU4 �����.�N��$��Ю��h��f>/X�S���]��D�Ho�<5\����dپƅtg���`2F �G�R�%SdM[�A0:T�0B���\��)0��h(7�N�aza���<6^�D�w�����UO���q��i4{��@!	�}��q��T��V4*5ސ<)�zt�A��B��p牆,���@L��gՃ���Q��p{��r�J�0��T1��O��@�xv9Q�\������/������}#�@<f�cҨ�)�R�tB�(�B4K!Q�$T#�F.���pزTS����ȥ/�#� ���E��I���@��h�9Ew��d_������ߕ*<_��ϟ~w�tE�>���@`�"�<lp1J?��B��`Ӟ�t<>[�
�b��i t+|<_��6*]P�G�!�D�B%[`�E�r�ܑ�3zB|���1X�z#CJ��?�0U/��R��cWg*�&4�C��t �y:h���Iԇ�`@"�p��ӧ�"���CT�c�@<`�Ɔ> x�`kΌ9f�DHܐ�Ԃ�H@G� l0z����2ú�ʓ������"Q���e1`�(�?,I�l�p,�[�һz�V�PC��̣����YMi�U��`��	E���ނ�H>/�"B�i��Ȗ]6~���\��Aރ<��P���6X՗����ߖܢ᰾��D���-�BAÃy��뫫�zt�AI��C(��>_��$����?�:���d�������u��G�_��.W�.�@�����\
%_�C�ׇ�WQ,J/��_�H_6*��:���M�9���������Q��� ��U��:AW�I�^���1�#@gRƈ����p3��-���PV�ɖ����� �U��F���{�]T�_�4G�i�ޏz������{bT�D#��#�

,d-��l(
��Q	��!3���ԉO�*&_��tK�S�BT9H�������;f�M��@�sߕ���բ�U@F �|�y���\!��V苲}4Q����j��(�n���J��#�`jQ�@h��{���B�z
�^
���3~t��mAU^��xTT{IΗ�W�,��J�c�������iYg�?�ǫ����X�J��C��ſ�j�֔L$	��L��1�������g��� ���p�$�yS�@r�E�+[!OL�L(;9��<V]A�|F0UH����P
`�ysT~~%�����qq���Td���PTEP� ,B��`8@ñ�	�R�@a��AR�7�zX��]#£�1Al ���,�lh(.{��e��!!���y�Ӎ�1�J8H#y����U��1�DM%Q[C���Q�Z���(��K��N%�>���H�1S> �,KG�z�?2��e2�"�*��Y��#i����La�����~��He�sApЄQ1�mTK�>��Ϛ�k�w]���'�c1�W��
�*��X/[���<]�~��M*�H2��WAL���������� ��%��s�� g(�>�~;�L?�1p ���.�tl̶M:u_���p�<����ɇ_�`� 01wbP  ���d �JI^щC�2��J��Ew���p�#m( 
sa�̑aK#Ä�µ)c�"w'A	$����CQ�ǯ��_ZI�Cܐ�N��Է����<O�?��=B  �  �QP�6�Q(a�[�_������,���z /0��bq�C�_g�H IR7%�'<FM
��I�BV,�$'T��dPjy��J�s�k<����t��]�z���=��&�E0Jy�1��z�2���U"��n~��"ZD����RE�b�,X2`�L�nƫ�PB2������������z8
>��+ء�Ñg�V��Ŋ*B{��n�e����"+����:���#A01wb�  ���d �xH]Q�1|9i*"��eKoG�o��!먠��Wܵy0�SYLq��͏���h�E����ۿ8sz%P)�f� ����l�Q,�h��-��4���O��"�p�9�P�u_��# �0�
E5P�6�H�_�CX��/�����-�f\i��������!�����U���Hrߥ�l�9-�lބ 4V����G��y�Y��j^1D�����ڞ�w��A��֞qg��Z���h:�)�s&b5��gC<����Ҍ"!�t1�|k�1vИA�p_��aXg��Lb dG�(�.��0�S���J�����:3%Y����~�:�j��tok�4�x��5H)��6qF��4Ӊ�v��s��M'�F��5���e|K"/j���C�5��G�N)900dcf    �S��0z:��=��`l"'�'�2��^��(4����&;%'{���谊�w�O$�M��M*>�]��e�