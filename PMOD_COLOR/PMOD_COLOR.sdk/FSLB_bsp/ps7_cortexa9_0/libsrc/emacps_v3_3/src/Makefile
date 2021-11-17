import abc
from typing import Optional

from pip._vendor.pkg_resources import Distribution

from pip._internal.index.package_finder import PackageFinder
from pip._internal.req import InstallRequirement


class AbstractDistribution(metaclass=abc.ABCMeta):
    """A base class for handling installable artifacts.

    The requirements for anything installable are as follows:

     - we must be able to determine the requirement name
       (or we can't correctly handle the non-upgrade case).

     - for packages with setup requirements, we must also be able
       to determine their requirements without installing additional
       packages (for the same reason a