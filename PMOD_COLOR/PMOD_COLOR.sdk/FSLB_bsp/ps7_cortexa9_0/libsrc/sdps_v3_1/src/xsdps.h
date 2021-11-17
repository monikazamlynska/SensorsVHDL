a
    WH�`F  �                   @   sL  d Z ddlZddlZddlmZ ddlmZ ddlmZm	Z	m
Z
mZmZmZ ddlmZ ddlmZ ddlmZ dd	lmZmZmZmZmZ dd
lmZ ddlmZ ddlmZ ddl m!Z!m"Z" ddl#m$Z$ ddl%m&Z&m'Z' ddl(m)Z) ddl*m+Z+ ddl,m-Z-m.Z. ddl/m0Z0m1Z1 e�2e3�Z4ee5e
e! f Z6ddd�Z7G dd� de&�Z8dS )ay  Dependency Resolution

The dependency resolution in pip is performed as follows:

for top-level requirements:
    a. only one spec allowed per project, regardless of conflicts or not.
       otherwise a "double requirement" exception is raised
    b. they override sub-dependency requirements.
for sub-dependencies
    a. "first found, wins" (where the order is breadth first)
�    N)�defaultdict)�chain)�DefaultDict�Iterable�List�Optional�Set�Tuple)�
specifiers)�Distribution)�
WheelCache)�BestVersionAlreadyInstalled�DistributionNotFound�	HashError�
HashErrors�UnsupportedPythonVersion)�PackageFinder)�Link)�RequirementPreparer)�InstallRequirement�check_invalid_constraint_type)�RequirementSet)�BaseResolver�InstallRequirementProvider)�get_supported)�
indent_log)�dist_in_usersite�normalize_version_info)�check_requires_python�get_requires_pythonFc              
   C   s�   t | �}zt||d�}W n8 tjyP } zt�d| j|� W Y d}~dS d}~0 0 |rZdS d�tt	|��}|r�t�
d| j||� dS td�| j||���dS )a�  
    Check whether the given Python version is compatible with a distribution's
    "Requires-Python" value.

    :param version_info: A 3-tuple of ints representing the Python
        major-minor-micro version to check.
    :param ignore_requires_python: Whether to ignore the "Requires-Python"
        value if the given Python version isn't compatible.

    :raises UnsupportedPythonVersion: When the given Python version isn't
        compatible.
    )�version_infoz-Package %r has an invalid Requires-Python: %sN�.zBIgnoring failed Requires-Python check for package %r: %s not in %rz8Package {!r} requires a different Python: {} not in {!r})r   r   r
   �InvalidSpecifier�logger�warning�project_name�join�map�str�debugr   �format)�distr    �ignore_requires_python�requires_python�is_compatible�exc�version� r1   �L/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/resolution/legacy/resolver.py�_check_dist_requires_python4   s4    �
����r3   c                       sr   e Zd ZdZh d�Zd� fdd�	Zdd� Zdd	� Zd
d� Zdd� Z	dd� Z
dd� Zdd� Zdd� Zdd� Z�  ZS )�Resolverz�Resolves which packages need to be installed/uninstalled to perform     the requested operation without breaking the requirements of any package.
    >   �to-satisfy-only�only-if-needed�eagerNc                    s�   t � ��  |
| jv sJ �|d u r0tjd d� }nt|�}|| _|| _|| _|| _	|
| _
|	| _|| _|| _|| _|| _|| _tt�| _d S )N�   )�super�__init__�_allowed_strategies�sysr    r   �_py_version_info�preparer�finder�wheel_cache�upgrade_strategy�force_reinstall�ignore_dependencies�ignore_installedr,   �use_user_site�_make_install_reqr   �list�_discovered_dependencies)�selfr>   r?   r@   �make_install_reqrE   rC   rD   r,   rB   rA   �py_version_info��	__class__r1   r2   r:   l   s&    
�zResolver.__init__c                 C   s�   t |d�}|D ]}|jr t|� |�|� qg }t� }t|j|�D ]P}z|�| �||�� W qB t	y� } z||_
|�|� W Y d}~qBd}~0 0 qB|r�|�|S )a�  Resolve what operations need to be done

        As a side-effect of this method, the packages (and their dependencies)
        are downloaded, unpacked and prepared for installation. This
        preparation is done by ``pip.operations.prepare``.

        Once PyPI has static dependency metadata available, it would be
        possible to move the preparation to become a step separated from
        dependency resolution.
        )�check_supported_wheelsN)r   �
constraintr   �add_requirementr   r   �all_requirements�extend�_resolve_oner   �req�append)rI   �	root_reqsrN   �requirement_setrT   �discovered_reqs�hash_errorsr/   r1   r1   r2   �resolve�   s     
"zResolver.resolvec                 C   s:   | j dkrdS | j dkrdS | j dks*J �|jp4|jS d S )Nr5   Fr7   Tr6   )rA   �user_suppliedrO   �rI   rT   r1   r1   r2   �_is_upgrade_allowed�   s    

zResolver._is_upgrade_allowedc                 C   s    | j rt|j�rd|_d|_dS )z4
        Set a requirement to be installed.
        TN)rE   r   �satisfied_by�should_reinstallr\   r1   r1   r2   �_set_req_to_reinstall�   s    zResolver._set_req_to_reinstallc                 C   s�   | j r
dS |�| j� |js dS | jr4| �|� dS | �|�sP| jdkrLdS dS |js�z| j	j
|dd� W n$ ty~   Y dS  ty�   Y n0 | �|� dS )a  Check if req_to_install should be skipped.

        This will check if the req is installed, and whether we should upgrade
        or reinstall it, taking into account all the relevant user options.

        After calling this req_to_install will only have satisfied_by set to
        None if the req_to_install is to be upgraded/reinstalled etc. Any
        other value will be a dist recording the current thing installed that
        satisfies the requirement.

        Note that for vcs urls and the like we can't assess skipping in this
        routine - we simply identify that we need to pull the thing down,
        then later on it is pulled down and introspected to assess upgrade/
        reinstalls etc.

        :return: A text reason for why it was skipped, or None.
        Nr6   z#already satisfied, skipping upgradezalready satisfiedT)�upgradezalready up-to-date)rD   �check_if_existsrE   r^   rB   r`   r]   rA   �linkr?   �find_requirementr   r   )rI   �req_to_installr1   r1   r2   �_check_skip_installed�   s*    



zResolver._check_skip_installedc                 C   sR   | � |�}| j�||�}|s d S |j}|jrN|jp4d}dj||d�}t�|� |S )Nz<none given>zqThe candidate selected for download or install is a yanked version: {candidate}
Reason for being yanked: {reason})�	candidate�reason)	r]   r?   rd   rc   �	is_yanked�yanked_reasonr*   r#   r$   )rI   rT   ra   �best_candidaterc   rh   �msgr1   r1   r2   �_find_requirement_link  s    

��
zResolver._find_requirement_linkc                 C   s~   |j du r| �|�|_ | jdu s(| jjr,dS | jj|j |jt� d�}|durzt�	d|j � |j |j
u rr|jrrd|_|j |_ dS )af  Ensure that if a link can be found for this, that it is found.

        Note that req.link may still be None - if the requirement is already
        installed and not needed to be upgraded based on the return value of
        _is_upgrade_allowed().

        If preparer.require_hashes is True, don't use the wheel cache, because
        cached wheels, always built locally, have different hashes than the
        files downloaded from the index server and thus throw false hash
        mismatches. Furthermore, cached wheels at present have undeterministic
        contents due to file modification times.
        N)rc   �package_name�supported_tagszUsing cached wheel link: %sT)rc   rm   r@   r>   �require_hashes�get_cache_entry�namer   r#   r)   �original_link�
persistent�original_link_is_in_wheel_cache)rI   rT   �cache_entryr1   r1   r2   �_populate_link  s    
�zResolver._populate_linkc                 C   s�   |j r| j�|�S |jdu s J �| �|�}|jr>| j�||�S | �|� | j�|�}| jsf|�	| j
� |jr�| jdkp�| jp�| jp�|jjdk}|r�| �|� nt�d|� |S )zzTakes a InstallRequirement and returns a single AbstractDist         representing a prepared variant of the same.
        Nr5   �filez<Requirement already satisfied (use --upgrade to upgrade): %s)�editabler>   �prepare_editable_requirementr^   rf   �prepare_installed_requirementrw   �prepare_linked_requirementrD   rb   rE   rA   rB   rc   �schemer`   r#   �info)rI   rT   �skip_reasonr+   �should_modifyr1   r1   r2   �_get_dist_for8  s2    



��
��zResolver._get_dist_forc           	         s  �j s�jrg S d�_����}t|�j�jd� g � � ���fdd�}t� �� ���j�st�j	sfJ ��j
�dd� �js��jr�t�dd��j�� tt�j�t|j� �}|D ]}t�d	||� q�tt|j�t�j�@ �}|�|�D ]}|||d
� q�W d  � n1 �s0    Y  � S )zxPrepare a single requirements file.

        :return: A list of additional InstallRequirements to also install.
        T)r    r,   c                    sP   �� t| ���}�j}�j|||d�\}}|rB|rB�j| �|� � �|� d S )N)�parent_req_name�extras_requested)rF   r(   rr   rP   rH   rU   rR   )�subreqr�   �sub_install_reqr�   �to_scan_again�add_to_parent��	more_reqsre   rW   rI   r1   r2   �add_req�  s    ��
z&Resolver._resolve_one.<locals>.add_reqN)r�   z!Installing extra requirements: %r�,z"%s does not provide the extra '%s')r�   )rO   �preparedr�   r3   r=   r,   r   �has_requirementrr   r[   rP   rC   �extrasr#   r)   r&   �sorted�setr$   �requires)	rI   rW   re   r+   r�   �missing_requested�missing�available_requestedr�   r1   r�   r2   rS   g  s@    
�

���.zResolver._resolve_onec                    s8   g � t � �� ���fdd��|j�� D ]}�|� q&� S )z�Create the installation order.

        The installation order is topological - requirements are installed
        before the requiring thing. We break cycles at an arbitrary point,
        and make no other guarantees.
        c                    sN   | j s| �v rd S | jrd S ��| � �j| j D ]}�|� q2� �| � d S )N)r^   rO   �addrH   rr   rU   )rT   �dep��order�ordered_reqs�schedulerI   r1   r2   r�   �  s    

z1Resolver.get_installation_order.<locals>.schedule)r�   �requirements�values)rI   �req_set�install_reqr1   r�   r2   �get_installation_order�  s    
zResolver.get_installation_order)N)�__name__�
__module__�__qualname__�__doc__r;   r:   rZ   r]   r`   rf   rm   rw   r�   rS   r�   �__classcell__r1   r1   rL   r2   r4   e   s    �)$
5/Lr4   )F)9r�   �loggingr<   �collectionsr   �	itertoolsr   �typingr   r   r   r   r   r	   Zpip._vendor.packagingr
   Zpip._vendor.pkg_resourcesr   �pip._internal.cacher   �pip._internal.exceptionsr   r   r   r   r   �"pip._internal.index.package_finderr   �pip._internal.models.linkr   � pip._internal.operations.preparer   Zpip._internal.req.req_installr   r   Zpip._internal.req.req_setr   �pip._internal.resolution.baser   r   �&pip._internal.utils.compatibility_tagsr   �pip._internal.utils.loggingr   �pip._internal.utils.miscr   r   �pip._internal.utils.packagingr   r   �	getLoggerr�   r#   r(   ZDiscoveredDependenciesr3   r4   