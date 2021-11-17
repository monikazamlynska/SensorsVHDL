a
    WH�`�  �                   @   s8   d dl mZ d dlmZ d dlmZ G dd� de�ZdS )�    )�parse)�Link)�KeyBasedCompareMixinc                       s8   e Zd ZdZg d�Z� fdd�Zdd� Zdd� Z�  ZS )	�InstallationCandidatez9Represents a potential "candidate" for installation.
    )�name�version�linkc                    s6   || _ t|�| _|| _t� j| j | j| jftd� d S )N)�key�defining_class)r   �parse_versionr   r   �super�__init__r   )�selfr   r   r   ��	__class__� �B/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/models/candidate.pyr      s    
�zInstallationCandidate.__init__c                 C   s   d� | j| j| j�S )Nz)<InstallationCandidate({!r}, {!r}, {!r})>��formatr   r   r   �r   r   r   r   �__repr__   s    �zInstallationCandidate.__repr__c                 C   s   d� | j| j| j�S )Nz!{!r} candidate (version {} at {})r   r   r   r   r   �__str__   s    �zInstallationCandidate.__str__)	�__name__�
__module__�__qualname__�__doc__�	__slots__r   r   r   �__classcell__r   r   r   r   r      s
   r   N)�pip._vendor.packaging.versionr   r   �pip._internal.models.linkr   �pip._internal.utils.modelsr   r   r   r   r   r   �<module>   s                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     